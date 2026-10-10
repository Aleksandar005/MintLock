// DISC-ANCHOR: 4·a·c − b² == |D| na pravoj 2048-bit formi, LogUp range-check (bez bit-dekomp).
// Interno vezuje |D| za formu (a,c,b preko AC=a·c, BB=b²), umesto da |D| bude samo javni ulaz.
//
// Anchor po limbu (D<0 -> 4ac>b² -> obe strane nenegativne, unsigned carry):
//   LHS: 4·AC[k] + lcin == L[k] + RADIX·lcout
//   RHS: BB[k] + D[k] + rcin == R[k] + RADIX·rcout
//   ANCHOR: L[k] == R[k]
// Range-check: L[k],R[k] < 2^16 i lcarry<2^3, rcarry<2^2 -> SVE kroz JEDNU LogUp tablicu [0,2^16).
//   (bit-dekomp iz mulseg_c zamenjena; carry vrednosti su < 2^16 pa u istoj tablici.)
//
// Trag: N=65536 (== tablica). Aktivnih limba: 128 (2048-bit). Ostatak in-range padding.

use std::fs;
use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const RADIX: u64 = 1 << 16;
const N: usize = 1 << 16;   // 65536 == tablica [0,2^16) I dužina traga
const NL: usize = 128;      // aktivnih limba (2048-bit)

// glavne kolone
const ACc: usize = 0;   // AC[k] = (a·c)[k]
const BBc: usize = 1;   // BB[k] = (b²)[k]
const Dc:  usize = 2;   // D[k]  = |D|[k]
const LCIN:usize = 3;   // LHS carry-in
const L_C: usize = 4;   // LHS limb rezultata          -- range-check tok
const LCO: usize = 5;   // LHS carry-out (== nxt LCIN) -- range-check tok
const RCIN:usize = 6;
const R_C: usize = 7;   // RHS limb rezultata          -- range-check tok
const RCO: usize = 8;   // RHS carry-out               -- range-check tok
const T_C: usize = 9;   // tablica [0,N)
const M_L: usize = 10;  // mult za L
const M_R: usize = 11;  // mult za R
const M_LC:usize = 12;  // mult za LCO
const M_RC:usize = 13;  // mult za RCO
const CTR: usize = 14;  // pun stepen
const MAIN_W: usize = 15;

const NUM_LU: usize = 4;
const LU_VAL: [usize; NUM_LU] = [L_C, R_C, LCO, RCO];
const LU_MUL: [usize; NUM_LU] = [M_L, M_R, M_LC, M_RC];

struct AnchTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl AnchTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        AnchTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [NUM_LU], [1]), length }
    }
}
impl Trace for AnchTrace {
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
        let alpha = rand[0];
        let n = self.length;
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
        let cols: Vec<Vec<E>> = (0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect();
        Some(ColMatrix::new(cols))
    }
}

#[derive(Clone)]
struct Pub {
    ac0: BaseElement, bb0: BaseElement, d0: BaseElement,
    l0: BaseElement, r0: BaseElement, lco0: BaseElement, rco0: BaseElement,
    ml0: BaseElement, mr0: BaseElement, mlc0: BaseElement, mrc0: BaseElement,
    n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.ac0,self.bb0,self.d0,self.l0,self.r0,self.lco0,self.rco0,
             self.ml0,self.mr0,self.mlc0,self.mrc0,BaseElement::new(self.n as u64)]
    }
}

struct AnchAir { context: AirContext<BaseElement>, p: Pub }
impl Air for AnchAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main_deg = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(1), // CTR advance
            TransitionConstraintDegree::new(1), // LHS: 4AC+lcin == L + RADIX·lcout
            TransitionConstraintDegree::new(1), // RHS: BB+D+rcin == R + RADIX·rcout
            TransitionConstraintDegree::new(1), // LHS carry link: nxt LCIN == LCO
            TransitionConstraintDegree::new(1), // RHS carry link
            TransitionConstraintDegree::new(1), // ANCHOR L==R
        ];
        let aux_deg = vec![TransitionConstraintDegree::new(3); NUM_LU];
        // main asertacije: T0,CTR0,LCIN0=0,RCIN0=0 (4) + row0 (AC,BB,D,L,R,LCO,RCO)=7 = 11
        let n_main_assert = 4 + 7;
        let n_aux_assert = 2 * NUM_LU;
        let context = AirContext::new_multi_segment(ti, main_deg, aux_deg, n_main_assert, n_aux_assert, options);
        AnchAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));
        result[0] = nxt[T_C] - cur[T_C] - one;
        result[1] = nxt[CTR] - cur[CTR] - one;
        result[2] = four*cur[ACc] + cur[LCIN] - (cur[L_C] + radix*cur[LCO]);
        result[3] = cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_C] + radix*cur[RCO]);
        result[4] = nxt[LCIN] - cur[LCO];
        result[5] = nxt[RCIN] - cur[RCO];
        result[6] = cur[L_C] - cur[R_C]; // ANCHOR
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(LCIN, 0, BaseElement::ZERO),
            Assertion::single(RCIN, 0, BaseElement::ZERO),
            Assertion::single(ACc, 0, self.p.ac0),
            Assertion::single(BBc, 0, self.p.bb0),
            Assertion::single(Dc, 0, self.p.d0),
            Assertion::single(L_C, 0, self.p.l0),
            Assertion::single(R_C, 0, self.p.r0),
            Assertion::single(LCO, 0, self.p.lco0),
            Assertion::single(RCO, 0, self.p.rco0),
        ]
    }
    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let alpha = rand.get_segment_elements(0)[0];
        let mn = main.next();
        let t = E::from(mn[T_C]);
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]);
            let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j]; let sp = aux.next()[j];
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
    }
    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = |v0: BaseElement, m0: BaseElement| -> E {
            (alpha - E::from(v0)).inv() - E::from(m0) * alpha.inv()
        };
        let v0 = [self.p.l0, self.p.r0, self.p.lco0, self.p.rco0];
        let m0 = [self.p.ml0, self.p.mr0, self.p.mlc0, self.p.mrc0];
        let mut v = Vec::new();
        for j in 0..NUM_LU {
            v.push(Assertion::single(j, 0, term0(v0[j], m0[j])));
            v.push(Assertion::single(j, self.p.n - 1, E::ZERO));
        }
        v
    }
}

struct P { options: ProofOptions }
impl Prover for P {
    type BaseField = BaseElement; type Air = AnchAir; type Trace = AnchTrace;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let g = |c: usize| t.main.get(c, 0);
        Pub { ac0:g(ACc), bb0:g(BBc), d0:g(Dc), l0:g(L_C), r0:g(R_C), lco0:g(LCO), rco0:g(RCO),
              ml0:g(M_L), mr0:g(M_R), mlc0:g(M_LC), mrc0:g(M_RC), n:t.length() }
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
type H = Blake3_256<BaseElement>; type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;

fn read_limbs() -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/anchor128.txt")).expect("anchor128.txt");
    let mut it = txt.lines();
    let parse = |line: &str| -> Vec<u64> { line.trim().split(',').map(|x| x.parse().unwrap()).collect() };
    let ac = parse(it.next().unwrap()); let bb = parse(it.next().unwrap()); let d = parse(it.next().unwrap());
    (ac, bb, d)
}

#[derive(Clone,Copy)]
enum Tamper { None, BadD(usize), BadAC(usize), OutOfRange(usize,u64) }

fn build(ac: &[u64], bb: &[u64], d: &[u64], tamper: Tamper) -> (AnchTrace, Pub) {
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i]=BaseElement::new(i as u64); col[CTR][i]=BaseElement::new(i as u64); }
    let mut ac = ac.to_vec(); let mut d = d.to_vec();
    if let Tamper::BadD(k) = tamper { d[k] = d[k].wrapping_add(1); }
    if let Tamper::BadAC(k) = tamper { ac[k] = ac[k].wrapping_add(1); }
    let mut lcin=0u64; let mut rcin=0u64;
    for k in 0..NL {
        let ls = 4*ac[k] + lcin; let lco = ls/RADIX; let ll = ls%RADIX;
        let rs = bb[k] + d[k] + rcin; let rco = rs/RADIX; let rl = rs%RADIX;
        col[ACc][k]=BaseElement::new(ac[k]); col[BBc][k]=BaseElement::new(bb[k]); col[Dc][k]=BaseElement::new(d[k]);
        col[LCIN][k]=BaseElement::new(lcin); col[L_C][k]=BaseElement::new(ll); col[LCO][k]=BaseElement::new(lco);
        col[RCIN][k]=BaseElement::new(rcin); col[R_C][k]=BaseElement::new(rl); col[RCO][k]=BaseElement::new(rco);
        lcin=lco; rcin=rco;
    }
    if let Tamper::OutOfRange(k,val) = tamper { col[L_C][k]=BaseElement::new(val); }
    // multipliciteti
    for j in 0..NUM_LU {
        let (vc,mc)=(LU_VAL[j],LU_MUL[j]);
        let mut mult=vec![0u64;N];
        for i in 0..N { let v=col[vc][i].as_int(); if (v as usize)<N { mult[v as usize]+=1; } }
        for i in 0..N { col[mc][i]=BaseElement::new(mult[i]); }
    }
    let g=|c:&Vec<Vec<BaseElement>>,cc:usize| c[cc][0];
    let p=Pub{ ac0:g(&col,ACc),bb0:g(&col,BBc),d0:g(&col,Dc),l0:g(&col,L_C),r0:g(&col,R_C),
               lco0:g(&col,LCO),rco0:g(&col,RCO),ml0:g(&col,M_L),mr0:g(&col,M_R),
               mlc0:g(&col,M_LC),mrc0:g(&col,M_RC),n:N };
    (AnchTrace::new(col), p)
}

fn run(ac:&[u64],bb:&[u64],d:&[u64],tamper:Tamper,label:&str,expect_ok:bool){
    let (trace,pi)=build(ac,bb,d,tamper);
    let options=ProofOptions::new(36,8,16,FieldExtension::Quadratic,4,31);
    let prover=P{options};
    let res=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
        let t0=Instant::now(); let proof=prover.prove(trace).expect("prove");
        let pm=t0.elapsed().as_secs_f64()*1000.0; let pb=proof.to_bytes().len();
        let sec=proof.security_level::<H>(true);
        let mo=winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok=winterfell::verify::<AnchAir,H,RC>(proof,pi.clone(),&mo).is_ok();
        (pb,sec,pm,ok)
    }));
    match res {
        Ok((pb,sec,pm,ok))=>{
            println!("{}: verify={} (ocek {}) ; dokaz {:.1} KB ; prove {:.0} ms ; sec {}",
                label, if ok{"PASS"}else{"FAIL"}, if expect_ok{"PASS"}else{"FAIL"}, pb as f64/1024.0, pm, sec);
            if ok!=expect_ok { println!("   >>> NEOCEKIVANO!"); std::process::exit(2); }
        }
        Err(_)=>{ println!("{}: PANIC (ocek {})",label,if expect_ok{"PASS"}else{"FAIL"}); if expect_ok{std::process::exit(2);} }
    }
}

fn main(){
    println!("== DISC-ANCHOR: 4ac−b²==|D| na 2048-bit formi, LogUp range-check (bez bit-dekomp) ==");
    println!("glavne kolone: {} + aux (LogUp): {} = {} ; aktivnih limba: {} ; N={}\n",
             MAIN_W, NUM_LU, MAIN_W+NUM_LU, NL, N);
    let (ac,bb,d)=read_limbs();
    // sanity anchor
    let mut lcin=0u64; let mut rcin=0u64;
    for k in 0..NL {
        let ll=(4*ac[k]+lcin)%RADIX; let lco=(4*ac[k]+lcin)/RADIX;
        let rl=(bb[k]+d[k]+rcin)%RADIX; let rco=(bb[k]+d[k]+rcin)/RADIX;
        assert_eq!(ll,rl,"anchor pao @limb {}",k); lcin=lco; rcin=rco;
    }
    println!("sanity: anchor 4ac=b²+|D| drži na svih {} limba", NL);

    run(&ac,&bb,&d,Tamper::None, "[validan]   disc-anchor", true);
    run(&ac,&bb,&d,Tamper::BadD(40), "[negativan] |D|[40]+1 (anchor puca)", false);
    run(&ac,&bb,&d,Tamper::BadAC(70), "[negativan] AC[70]+1 (anchor puca)", false);
    run(&ac,&bb,&d,Tamper::OutOfRange(20,70000), "[negativan] L[20]=70000 (van tablice, LogUp)", false);

    println!("\nSVE PROSLO: |D| interno vezan za formu preko anchor-a; LogUp range-check.");
}
