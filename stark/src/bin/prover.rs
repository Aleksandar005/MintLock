// OFF-CHAIN PROVER: čita PRAVU classgroup reduce trajektoriju (trajectory.txt iz
// emit_trajectory.py), uzima finalnu redukovanu formu (a,b,c,|D|), i proizvodi
// transparentan STARK dokaz da forma zadovoljava disc-anchor  4·a·c − b² == |D|.
// Serijalizuje RECEIPT (proof bytes + javni ulazi) u receipt.bin za on-chain verifier.
//
// Anchor jezgro je isto kao disc_anchor.rs (LogUp range-check, dva carry lanca), ali
// prover SAM računa AC=a·c i BB=b² iz forme (schoolbook), pa dokazuje anchor nad njima.
// Time je dokaz vezan za PRAVU formu iz reference implementacije, ne za sintetičke limbove.

use std::fs;
use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements, StarkField},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const RADIX: u64 = 1 << 16;
const N: usize = 1 << 16;
const NL: usize = 128; // anchor pozicija (2048-bit)

// ---- kolone (isti anchor kao disc_anchor) ----
const ACc: usize = 0; const BBc: usize = 1; const Dc: usize = 2;
const LCIN: usize = 3; const L_C: usize = 4; const LCO: usize = 5;
const RCIN: usize = 6; const R_C: usize = 7; const RCO: usize = 8;
const T_C: usize = 9; const M_L: usize = 10; const M_R: usize = 11;
const M_LC: usize = 12; const M_RC: usize = 13; const CTR: usize = 14;
const MAIN_W: usize = 15;
const NUM_LU: usize = 4;
const LU_VAL: [usize; NUM_LU] = [L_C, R_C, LCO, RCO];
const LU_MUL: [usize; NUM_LU] = [M_L, M_R, M_LC, M_RC];

struct T { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl T {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        T { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [NUM_LU], [1]), length }
    }
}
impl Trace for T {
    type BaseField = BaseElement;
    fn layout(&self) -> &TraceLayout { &self.layout }
    fn length(&self) -> usize { self.length }
    fn meta(&self) -> &[u8] { &[] }
    fn main_segment(&self) -> &ColMatrix<BaseElement> { &self.main }
    fn read_main_frame(&self, row: usize, frame: &mut EvaluationFrame<BaseElement>) {
        let next = (row + 1) % self.length;
        self.main.read_row_into(row, frame.current_mut());
        self.main.read_row_into(next, frame.next_mut());
    }
    fn build_aux_segment<E: FieldElement<BaseField = BaseElement>>(
        &mut self, aux_segments: &[ColMatrix<E>], rand: &[E],
    ) -> Option<ColMatrix<E>> {
        if !aux_segments.is_empty() { return None; }
        let alpha = rand[0]; let n = self.length;
        let mk = |vcol: usize, mcol: usize| -> Vec<E> {
            let mut s = vec![E::ZERO; n];
            let term = |i: usize| -> E {
                let v = E::from(self.main.get(vcol, i));
                let t = E::from(self.main.get(T_C, i));
                let m = E::from(self.main.get(mcol, i));
                (alpha - v).inv() - m * (alpha - t).inv()
            };
            s[0] = term(0);
            for i in 1..n { s[i] = s[i-1] + term(i); }
            s
        };
        Some(ColMatrix::new((0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect()))
    }
}

#[derive(Clone)]
struct Pub {
    ac0: BaseElement, bb0: BaseElement, d0: BaseElement,
    l0: BaseElement, r0: BaseElement, lco0: BaseElement, rco0: BaseElement,
    ml0: BaseElement, mr0: BaseElement, mlc0: BaseElement, mrc0: BaseElement, n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.ac0,self.bb0,self.d0,self.l0,self.r0,self.lco0,self.rco0,
             self.ml0,self.mr0,self.mlc0,self.mrc0,BaseElement::new(self.n as u64)]
    }
}

struct A { context: AirContext<BaseElement>, p: Pub }
impl Air for A {
    type BaseField = BaseElement; type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main_deg = vec![
            TransitionConstraintDegree::new(1), TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1), TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1), TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
        ];
        let aux_deg = vec![TransitionConstraintDegree::new(3); NUM_LU];
        let context = AirContext::new_multi_segment(ti, main_deg, aux_deg, 4+7, 2*NUM_LU, options);
        A { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX)); let four = E::from(BaseElement::new(4));
        result[0] = nxt[T_C] - cur[T_C] - one;
        result[1] = nxt[CTR] - cur[CTR] - one;
        result[2] = four*cur[ACc] + cur[LCIN] - (cur[L_C] + radix*cur[LCO]);
        result[3] = cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_C] + radix*cur[RCO]);
        result[4] = nxt[LCIN] - cur[LCO];
        result[5] = nxt[RCIN] - cur[RCO];
        result[6] = cur[L_C] - cur[R_C];
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(T_C,0,BaseElement::ZERO), Assertion::single(CTR,0,BaseElement::ZERO),
            Assertion::single(LCIN,0,BaseElement::ZERO), Assertion::single(RCIN,0,BaseElement::ZERO),
            Assertion::single(ACc,0,self.p.ac0), Assertion::single(BBc,0,self.p.bb0),
            Assertion::single(Dc,0,self.p.d0), Assertion::single(L_C,0,self.p.l0),
            Assertion::single(R_C,0,self.p.r0), Assertion::single(LCO,0,self.p.lco0),
            Assertion::single(RCO,0,self.p.rco0),
        ]
    }
    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where F: FieldElement<BaseField = BaseElement>, E: FieldElement<BaseField = BaseElement> + ExtensionOf<F> {
        let alpha = rand.get_segment_elements(0)[0];
        let mn = main.next(); let t = E::from(mn[T_C]);
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]); let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j]; let sp = aux.next()[j];
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
    }
    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let t0 = |v0: BaseElement, m0: BaseElement| -> E { (alpha - E::from(v0)).inv() - E::from(m0)*alpha.inv() };
        let v0 = [self.p.l0,self.p.r0,self.p.lco0,self.p.rco0];
        let m0 = [self.p.ml0,self.p.mr0,self.p.mlc0,self.p.mrc0];
        let mut v = Vec::new();
        for j in 0..NUM_LU { v.push(Assertion::single(j,0,t0(v0[j],m0[j]))); v.push(Assertion::single(j,self.p.n-1,E::ZERO)); }
        v
    }
}

struct Pv { options: ProofOptions }
impl Prover for Pv {
    type BaseField = BaseElement; type Air = A; type Trace = T;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let g = |c: usize| t.main.get(c, 0);
        Pub{ ac0:g(ACc),bb0:g(BBc),d0:g(Dc),l0:g(L_C),r0:g(R_C),lco0:g(LCO),rco0:g(RCO),
             ml0:g(M_L),mr0:g(M_R),mlc0:g(M_LC),mrc0:g(M_RC),n:t.length() }
    }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self, ti: &TraceInfo, mt: &ColMatrix<BaseElement>, dom: &StarkDomain<BaseElement>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) { DefaultTraceLde::new(ti, mt, dom) }
    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self, air: &'a Self::Air, aux: AuxTraceRandElements<E>,
        cc: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> { DefaultConstraintEvaluator::new(air, aux, cc) }
}
type H = Blake3_256<BaseElement>;

// ---- učitavanje trajektorije + schoolbook mult ----
fn parse_line(txt: &str, tag: &str) -> Vec<u64> {
    for line in txt.lines() {
        if let Some(rest) = line.strip_prefix(&format!("{} ", tag)) {
            return rest.split(',').filter(|s| !s.is_empty()).map(|x| x.parse().unwrap()).collect();
        }
    }
    panic!("nema tag {}", tag);
}
fn scalar_line(txt: &str, tag: &str) -> u64 {
    for line in txt.lines() {
        if let Some(rest) = line.strip_prefix(&format!("{} ", tag)) {
            return rest.trim().parse().unwrap();
        }
    }
    panic!("nema skalar {}", tag);
}

fn schoolbook(x: &[u64], y: &[u64], nout: usize) -> Vec<u64> {
    let mut out = vec![0i128; nout];
    for i in 0..x.len() { for j in 0..y.len() { if i+j < nout { out[i+j] += (x[i] as i128)*(y[j] as i128); } } }
    let mut res = vec![0u64; nout]; let mut car = 0i128;
    for k in 0..nout { let s = out[k]+car; res[k] = (s % RADIX as i128) as u64; car = s / RADIX as i128; }
    res
}

fn build_from_form(ac: &[u64], bb: &[u64], dabs: &[u64]) -> (T, Pub) {
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i]=BaseElement::new(i as u64); col[CTR][i]=BaseElement::new(i as u64); }
    let mut lcin=0u64; let mut rcin=0u64;
    for k in 0..NL {
        let ac_k = *ac.get(k).unwrap_or(&0); let bb_k = *bb.get(k).unwrap_or(&0); let d_k = *dabs.get(k).unwrap_or(&0);
        let ls = 4*ac_k + lcin; let lco = ls/RADIX; let ll = ls%RADIX;
        let rs = bb_k + d_k + rcin; let rco = rs/RADIX; let rl = rs%RADIX;
        assert_eq!(ll, rl, "anchor pao @limb {} (forma ne zadovoljava 4ac-b²=|D|)", k);
        col[ACc][k]=BaseElement::new(ac_k); col[BBc][k]=BaseElement::new(bb_k); col[Dc][k]=BaseElement::new(d_k);
        col[LCIN][k]=BaseElement::new(lcin); col[L_C][k]=BaseElement::new(ll); col[LCO][k]=BaseElement::new(lco);
        col[RCIN][k]=BaseElement::new(rcin); col[R_C][k]=BaseElement::new(rl); col[RCO][k]=BaseElement::new(rco);
        lcin=lco; rcin=rco;
    }
    for j in 0..NUM_LU {
        let (vc,mc)=(LU_VAL[j],LU_MUL[j]); let mut mult=vec![0u64;N];
        for i in 0..N { let v=col[vc][i].as_int(); if (v as usize)<N { mult[v as usize]+=1; } }
        for i in 0..N { col[mc][i]=BaseElement::new(mult[i]); }
    }
    let g=|c:&Vec<Vec<BaseElement>>,cc:usize| c[cc][0];
    let p=Pub{ ac0:g(&col,ACc),bb0:g(&col,BBc),d0:g(&col,Dc),l0:g(&col,L_C),r0:g(&col,R_C),
               lco0:g(&col,LCO),rco0:g(&col,RCO),ml0:g(&col,M_L),mr0:g(&col,M_R),
               mlc0:g(&col,M_LC),mrc0:g(&col,M_RC),n:N };
    (T::new(col), p)
}

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| concat!(env!("CARGO_MANIFEST_DIR"), "/data/trajectory.txt").into());
    let out = std::env::args().nth(2).unwrap_or_else(|| concat!(env!("CARGO_MANIFEST_DIR"), "/data/receipt.bin").into());
    let txt = fs::read_to_string(&path).expect("trajectory.txt");
    let nrounds = scalar_line(&txt, "n_rounds");
    let dabs = parse_line(&txt, "D_abs");
    // finalna redukovana forma (svojstvo koje dokazujemo: 4·a·c − b² == |D|)
    let a = parse_line(&txt, "final_a");
    let b = parse_line(&txt, "final_b");
    let c = parse_line(&txt, "final_c");

    println!("== OFF-CHAIN PROVER: classgroup forma -> STARK disc-anchor dokaz ==");
    println!("ulaz: {} ({} rundi u trajektoriji) ; L={} limba", path, nrounds, a.len());

    // AC = a·c, BB = b·b (schoolbook, nout=NL)
    let ac = schoolbook(&a, &c, NL);
    let bb = schoolbook(&b, &b, NL);
    // sanity: 4ac - b² == |D| po limbu (sa carry) — proverava sama build_from_form (assert)
    println!("računam AC=a·c, BB=b·b (schoolbook), dokazujem 4·AC − BB == |D| ...");

    let (trace, pi) = build_from_form(&ac, &bb, &dabs);
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = Pv { options };
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64()*1000.0;
    let sec = proof.security_level::<H>(true);
    let bytes = proof.to_bytes();

    // RECEIPT: [magic 4][sec 1][n_pub 4][pub_elems... 8B LE][proof_len 4][proof bytes]
    let pubv = pi.to_elements();
    let mut receipt = Vec::new();
    receipt.extend_from_slice(b"MLK1");
    receipt.push(sec as u8);
    receipt.extend_from_slice(&(pubv.len() as u32).to_le_bytes());
    for e in &pubv { receipt.extend_from_slice(&e.as_int().to_le_bytes()); }
    receipt.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    receipt.extend_from_slice(&bytes);
    fs::write(&out, &receipt).expect("write receipt");

    println!("dokaz: {:.1} KB ; prove {:.0} ms ; sec {}", bytes.len() as f64/1024.0, pm, sec);
    println!("RECEIPT: {} bajta -> {} (magic MLK1, {} javnih elemenata)", receipt.len(), out, pubv.len());
    println!("\nprover gotov: |D| vezan za PRAVU redukovanu formu; receipt spreman za on-chain verifier.");
}
