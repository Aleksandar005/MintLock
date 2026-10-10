// DISC-FULL L=64: puno vezivanje |D| ← a,b,c na PUNOJ širini (1024-bit operandi, 2048-bit proizvod).
// Skalirano iz disc_full (L=4 demo). Ključna izmena: one-hot POS (koji na L=64 daje 256 kol > 255)
// zamenjen SLIDING-WINDOW konvolucijom (mulseg_b obrazac): conv[k] = Σ_i A[i]·WIN[i], WIN klizi.
// Time širina padne na ~150 kol < 255.
//
// Tri faze u jednom tragu, perm-vezane (grand-product), LogUp range-check:
//   MULT_AC:  AC[k] = (a·c)[k]   (a broadcast, c kroz window)
//   MULT_BB:  BB[k] = (b·b)[k]   (b broadcast, b kroz window)
//   ANCHOR:   4·AC[k] − BB[k] == |D|[k]
// Carry konvolucije ide do ~2^21 (> tablice 2^16) -> razložen na cnext_lo (16-bit) + cnext_hi (5-bit),
// oba LogUp-check protiv iste tablice [0,2^16). |D| interno izveden iz a,b,c.

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
const N: usize = 1 << 16;     // 65536 == deljena tablica [0,2^16) I dužina traga
const L: usize = 64;          // limba u a,b,c (1024-bit)
const NPOS: usize = 2*L;      // 128 izlaznih pozicija (2048-bit proizvod)
const PH_AC: usize = 0;
const PH_BB: usize = NPOS;    // 128
const PH_AN: usize = 2*NPOS;  // 256
const PH_BBC: usize = 3*NPOS; // 384  (anchor troši BB, perm imenilac)
const ACTIVE: usize = 4*NPOS; // 512

// glavne kolone
const AW: usize = 0;                 // A broadcast (operand1), L
const WIN: usize = AW + L;           // sliding window (operand2), L
const CIN: usize = WIN + L;          // conv carry-in (do 2^21)
const PRODC: usize = CIN + 1;        // proizvod limb                        -- range-check
const CNLO: usize = PRODC + 1;       // cnext lo 16-bit                      -- range-check
const CNHI: usize = CNLO + 1;        // cnext hi ~5-bit                      -- range-check
// anchor
const ACc: usize = CNHI + 1;
const BBc: usize = ACc + 1;
const Dc:  usize = BBc + 1;
const LCIN: usize = Dc + 1;
const L_C: usize = LCIN + 1;         // LHS limb                             -- range-check
const LCO: usize = L_C + 1;
const RCIN: usize = LCO + 1;
const R_C: usize = RCIN + 1;         // RHS limb                             -- range-check
const RCO: usize = R_C + 1;
// faze + perm
const FMUL: usize = RCO + 1;
const FANC: usize = FMUL + 1;
const TAGP: usize = FANC + 1;
const TAGA: usize = TAGP + 1;
const PVAL: usize = TAGA + 1;
const PSEL: usize = PVAL + 1;
// tablica + LogUp mult
const T_C: usize = PSEL + 1;
const M_PR: usize = T_C + 1;
const M_CL: usize = M_PR + 1;
const M_CH: usize = M_CL + 1;
const M_L: usize = M_CH + 1;
const M_R: usize = M_L + 1;
const CTR: usize = M_R + 1;
const MAIN_W: usize = CTR + 1;

const NUM_LU: usize = 5; // PRODC, CNLO, CNHI, L_C, R_C
const LU_VAL: [usize; NUM_LU] = [PRODC, CNLO, CNHI, L_C, R_C];
const LU_MUL: [usize; NUM_LU] = [M_PR, M_CL, M_CH, M_L, M_R];
const AUX_Z: usize = NUM_LU;
const AUX_W: usize = NUM_LU + 1;

struct DTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl DTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        DTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [AUX_W], [2]), length }
    }
}
impl Trace for DTrace {
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
        let alpha = rand[0]; let gamma = rand[1]; let beta = gamma*gamma;
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
        let mut cols: Vec<Vec<E>> = (0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect();
        let mut z = vec![E::ONE; n]; let mut acc = E::ONE;
        for i in 0..n {
            z[i] = acc;
            if self.main.get(PSEL, i) == BaseElement::ONE {
                let val = E::from(self.main.get(PVAL, i));
                if self.main.get(FMUL, i) == BaseElement::ONE {
                    acc = acc * (beta - (E::from(self.main.get(TAGP, i)) + gamma*val));
                } else {
                    acc = acc * (beta - (E::from(self.main.get(TAGA, i)) + gamma*val)).inv();
                }
            }
        }
        cols.push(z);
        Some(ColMatrix::new(cols))
    }
}

#[derive(Clone)]
struct MRow {
    aw: Vec<BaseElement>, win: Vec<BaseElement>,
    win0_ac: Vec<BaseElement>, win0_bb: Vec<BaseElement>,
    prod0: BaseElement, cnlo0: BaseElement, cnhi0: BaseElement,
    mpr0: BaseElement, mcl0: BaseElement, mch0: BaseElement, ml0: BaseElement, mr0: BaseElement,
}
#[derive(Clone)]
struct Pub { n: usize, m: MRow }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = vec![BaseElement::new(self.n as u64)];
        v.extend_from_slice(&self.m.aw); v.extend_from_slice(&self.m.win);
        v.extend_from_slice(&self.m.win0_ac); v.extend_from_slice(&self.m.win0_bb);
        v.push(self.m.prod0); v.push(self.m.cnlo0); v.push(self.m.cnhi0);
        v.push(self.m.mpr0); v.push(self.m.mcl0); v.push(self.m.mch0); v.push(self.m.ml0); v.push(self.m.mr0);
        v
    }
}

struct DAir { context: AirContext<BaseElement>, m: MRow }
impl Air for DAir {
    type BaseField = BaseElement; type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let d = vec![
            TransitionConstraintDegree::new(1), // T
            TransitionConstraintDegree::new(1), // CTR
            TransitionConstraintDegree::new(2), // MULT conv+carry
            TransitionConstraintDegree::new(2), // MULT carry link
            TransitionConstraintDegree::new(2), // ANCHOR LHS
            TransitionConstraintDegree::new(2), // ANCHOR RHS
            TransitionConstraintDegree::new(2), // ANCHOR LHS carry link
            TransitionConstraintDegree::new(2), // ANCHOR RHS carry link
            TransitionConstraintDegree::new(2), // ANCHOR L==R
        ];
        // + WIN shift: L-1 constraint-a (WIN[i]'=WIN[i-1]) gejtano da ne curi na granicu faze
        let mut d = d;
        for _ in 1..L { d.push(TransitionConstraintDegree::new(2)); }
        let mut aux = vec![TransitionConstraintDegree::new(3); NUM_LU];
        aux.push(TransitionConstraintDegree::new(4)); // grand-product (psel·fanc·zp·ea)
        // main assert: T0,CTR0,CIN0=0 (3) + AW(L)+WIN(L) row0 + PRODC0,CNLO0,CNHI0 (3)
        //   + WIN[0] feed: (NPOS-1) AC + NPOS BB
        let n_main = 3 + L + L + 3 + (NPOS-1) + NPOS;
        let n_aux = 2*NUM_LU + 2;
        let context = AirContext::new_multi_segment(ti, d, aux, n_main, n_aux, options);
        DAir { context, m: p.m }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));
        let fmul = cur[FMUL]; let fanc = cur[FANC];
        let fmul_next = nxt[FMUL]; // da shift ne curi na granicu faze
        result[0] = nxt[T_C] - cur[T_C] - one;
        result[1] = nxt[CTR] - cur[CTR] - one;
        let mut conv = E::ZERO;
        for i in 0..L { conv += cur[AW+i]*cur[WIN+i]; }
        let cnext = cur[CNLO] + radix*cur[CNHI];
        result[2] = fmul * (cur[CIN] + conv - (cur[PRODC] + radix*cnext));
        result[3] = fmul * (nxt[CIN] - cnext);
        result[4] = fanc * (four*cur[ACc] + cur[LCIN] - (cur[L_C] + radix*cur[LCO]));
        result[5] = fanc * (cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_C] + radix*cur[RCO]));
        result[6] = fanc * (nxt[LCIN] - cur[LCO]);
        result[7] = fanc * (nxt[RCIN] - cur[RCO]);
        result[8] = fanc * (cur[L_C] - cur[R_C]);
        // WIN shift unutar mult faze: WIN[i]' == WIN[i-1] kada su i tekući i sledeći red MULT
        let gate = fmul * fmul_next;
        for i in 1..L { result[8+i] = gate * (nxt[WIN+i] - cur[WIN+i-1]); }
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(CIN, 0, BaseElement::ZERO),
            Assertion::single(PRODC, 0, self.m.prod0),
            Assertion::single(CNLO, 0, self.m.cnlo0),
            Assertion::single(CNHI, 0, self.m.cnhi0),
        ];
        for i in 0..L { v.push(Assertion::single(AW+i, 0, self.m.aw[i])); }
        for i in 0..L { v.push(Assertion::single(WIN+i, 0, self.m.win[i])); }
        // WIN[0] po redu = ulazni limb (c[k] u AC fazi, b[k] u BB fazi) — hrani window.
        // (PH_AC+0 je već vezan preko WIN+0 row0 asertacije -> počinjemo AC od k=1)
        for k in 1..NPOS { v.push(Assertion::single(WIN, PH_AC + k, self.m.win0_ac[k])); }
        for k in 0..NPOS { v.push(Assertion::single(WIN, PH_BB + k, self.m.win0_bb[k])); }
        v
    }
    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let alpha = rand.get_segment_elements(0)[0];
        let gamma = rand.get_segment_elements(0)[1];
        let beta = gamma*gamma;
        let mn = main.next();
        let t = E::from(mn[T_C]);
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]); let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j]; let sp = aux.next()[j];
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
        let mc = main.current();
        let psel = E::from(mc[PSEL]); let fmul = E::from(mc[FMUL]); let fanc = E::from(mc[FANC]);
        let val = E::from(mc[PVAL]);
        let ep = E::from(mc[TAGP]) + gamma*val;
        let ea = E::from(mc[TAGA]) + gamma*val;
        let z = aux.current()[AUX_Z]; let zp = aux.next()[AUX_Z];
        let mul_term = zp - z*(beta - ep);
        let anc_term = zp*(beta - ea) - z;
        let idle = zp - z;
        result[NUM_LU] = psel*(fmul*mul_term + fanc*anc_term) + (E::ONE - psel)*idle;
    }
    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = |v0: BaseElement, m0: BaseElement| -> E {
            (alpha - E::from(v0)).inv() - E::from(m0) * alpha.inv()
        };
        let v0 = [self.m.prod0, self.m.cnlo0, self.m.cnhi0, BaseElement::ZERO, BaseElement::ZERO];
        let m0 = [self.m.mpr0, self.m.mcl0, self.m.mch0, self.m.ml0, self.m.mr0];
        let mut v = Vec::new();
        for j in 0..NUM_LU {
            v.push(Assertion::single(j, 0, term0(v0[j], m0[j])));
            v.push(Assertion::single(j, self.context.trace_len() - 1, E::ZERO));
        }
        v.push(Assertion::single(AUX_Z, 0, E::ONE));
        v.push(Assertion::single(AUX_Z, ACTIVE, E::ONE));
        v
    }
}

struct P { options: ProofOptions, m: MRow }
impl Prover for P {
    type BaseField = BaseElement; type Air = DAir; type Trace = DTrace;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> Pub { Pub { n: N, m: self.m.clone() } }
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

fn conv_mul(x: &[u64], y: &[u64]) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    // vraća (prod, cnlo, cnhi) po poziciji
    let mut out = vec![0i128; NPOS];
    for i in 0..L { for j in 0..L { out[i+j] += (x[i] as i128)*(y[j] as i128); } }
    let (mut prod, mut cnlo, mut cnhi) = (vec![0u64;NPOS], vec![0u64;NPOS], vec![0u64;NPOS]);
    let mut carry = 0i128;
    for k in 0..NPOS {
        let s = out[k] + carry;
        prod[k] = (s % RADIX as i128) as u64;
        let cn = (s / RADIX as i128) as u64;    // cnext
        cnlo[k] = cn % RADIX; cnhi[k] = cn / RADIX;
        carry = cn as i128;
    }
    (prod, cnlo, cnhi)
}

#[derive(Clone,Copy)]
enum Tamper { None, BadProd, BadD, BreakLink }

fn build(a:&[u64], b:&[u64], c:&[u64], tamper: Tamper) -> (DTrace, MRow) {
    let (ac, _, _) = conv_mul(a,c);
    let (bb, _, _) = conv_mul(b,b);
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i]=BaseElement::new(i as u64); col[CTR][i]=BaseElement::new(i as u64); }

    // mult faza sa sliding-window: A=x broadcast; window WIN[i] na redu k = y[k-i] (0<=k-i<L)
    let fill_mult = |col: &mut Vec<Vec<BaseElement>>, base: usize, x:&[u64], y:&[u64],
                     prod:&[u64], cnlo:&[u64], cnhi:&[u64], tagbase: u64| {
        for k in 0..NPOS {
            let i = base + k;
            for t in 0..L { col[AW+t][i]=BaseElement::new(x[t]); }
            for t in 0..L {
                let idx = k as i64 - t as i64;
                let wv = if idx>=0 && (idx as usize) < L { y[idx as usize] } else { 0 };
                col[WIN+t][i]=BaseElement::new(wv);
            }
            // CIN = carry ulaz = cnext prethodnog reda (cnlo/hi[k-1]); k=0 -> 0
            let cin = if k==0 {0u64} else { cnlo[k-1] + RADIX*cnhi[k-1] };
            col[CIN][i]=BaseElement::new(cin);
            col[PRODC][i]=BaseElement::new(prod[k]);
            col[CNLO][i]=BaseElement::new(cnlo[k]); col[CNHI][i]=BaseElement::new(cnhi[k]);
            col[FMUL][i]=BaseElement::ONE;
            col[PSEL][i]=BaseElement::ONE;
            col[TAGP][i]=BaseElement::new(tagbase + k as u64);
            col[PVAL][i]=BaseElement::new(prod[k]);
        }
    };
    let (acx, aclo, achi) = { let (mut p,l,h)=conv_mul(a,c); if let Tamper::BadProd=tamper { p[3]=p[3].wrapping_add(1); } (p,l,h) };
    fill_mult(&mut col, PH_AC, a, c, &acx, &aclo, &achi, 0);
    let (bbx, bblo, bbhi) = conv_mul(b,b);
    fill_mult(&mut col, PH_BB, b, b, &bbx, &bblo, &bbhi, NPOS as u64);

    // ANCHOR faza: 4AC - BB == D ; troši AC (perm imenilac)
    let mut lcin=0i128; let mut rcin=0i128;
    for k in 0..NPOS {
        let i = PH_AN + k;
        let acv = ac[k] as i128; let bbv = bb[k] as i128;
        let ls = 4*acv + lcin; let lco = ls.div_euclid(RADIX as i128); let ll = ls.rem_euclid(RADIX as i128);
        let mut dval = ll - bbv - rcin; let mut rco = 0i128;
        while dval < 0 { dval += RADIX as i128; rco += 1; }
        let mut dstore = dval;
        if let Tamper::BadD = tamper { if k==3 { dstore += 1; } }
        col[ACc][i]=BaseElement::new(ac[k]); col[BBc][i]=BaseElement::new(bb[k]); col[Dc][i]=BaseElement::new(dstore as u64);
        col[LCIN][i]=BaseElement::new(lcin as u64); col[L_C][i]=BaseElement::new(ll as u64); col[LCO][i]=BaseElement::new(lco as u64);
        col[RCIN][i]=BaseElement::new(rcin as u64); col[R_C][i]=BaseElement::new(ll as u64); col[RCO][i]=BaseElement::new(rco as u64);
        col[FANC][i]=BaseElement::ONE;
        col[PSEL][i]=BaseElement::ONE;
        col[TAGA][i]=BaseElement::new((0*NPOS + k) as u64);
        col[PVAL][i]=BaseElement::new(ac[k]);
        lcin = lco; rcin = rco;
    }
    // BB-troši faza (perm imenilac)
    for k in 0..NPOS {
        let i = PH_BBC + k;
        col[PSEL][i]=BaseElement::ONE;
        col[TAGA][i]=BaseElement::new((NPOS + k) as u64);
        col[PVAL][i]=BaseElement::new(bb[k]);
    }
    if let Tamper::BreakLink = tamper { col[PVAL][PH_AN+2] = col[PVAL][PH_AN+2] + BaseElement::ONE; }

    for (vc,mc) in [(PRODC,M_PR),(CNLO,M_CL),(CNHI,M_CH),(L_C,M_L),(R_C,M_R)] {
        let mut mult=vec![0u64;N];
        for i in 0..N { let v=col[vc][i].as_int(); if (v as usize)<N { mult[v as usize]+=1; } }
        for i in 0..N { col[mc][i]=BaseElement::new(mult[i]); }
    }

    let m = MRow {
        aw: (0..L).map(|t| col[AW+t][0]).collect(),
        win:(0..L).map(|t| col[WIN+t][0]).collect(),
        win0_ac: (0..NPOS).map(|k| col[WIN][PH_AC+k]).collect(),
        win0_bb: (0..NPOS).map(|k| col[WIN][PH_BB+k]).collect(),
        prod0: col[PRODC][0], cnlo0: col[CNLO][0], cnhi0: col[CNHI][0],
        mpr0: col[M_PR][0], mcl0: col[M_CL][0], mch0: col[M_CH][0], ml0: col[M_L][0], mr0: col[M_R][0],
    };
    (DTrace::new(col), m)
}

fn run(a:&[u64],b:&[u64],c:&[u64],tamper:Tamper,label:&str,expect_ok:bool){
    let (trace,m)=build(a,b,c,tamper);
    let options=ProofOptions::new(36,8,16,FieldExtension::Quadratic,4,31);
    let prover=P{options, m: m.clone()};
    let res=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
        let t0=Instant::now(); let proof=prover.prove(trace).expect("prove");
        let pm=t0.elapsed().as_secs_f64()*1000.0; let pb=proof.to_bytes().len();
        let sec=proof.security_level::<H>(true);
        let mo=winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok=winterfell::verify::<DAir,H,RC>(proof, Pub{n:N, m:m.clone()}, &mo).is_ok();
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
    println!("== DISC-FULL L=64: |D|←a,b,c na PUNOJ širini (sliding-window mult, bez one-hot 255-zida) ==");
    println!("faze MULT_AC/MULT_BB/ANCHOR perm-vezane ; L={} ; kolone {} (<255) ; aktivnih redova {}\n",
             L, MAIN_W+AUX_W, ACTIVE);
    let mut rng=0x2024u64;
    let mut nx=|| { rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; rng%RADIX };
    let a:Vec<u64>=(0..L).map(|_| nx()).collect();
    let c:Vec<u64>=(0..L).map(|_| nx()).collect();
    let b:Vec<u64>=(0..L).map(|_| nx()).collect();
    run(&a,&b,&c,Tamper::None, "[validan]   |D| vezan za a,b,c (L=64)", true);
    run(&a,&b,&c,Tamper::BadProd, "[negativan] AC proizvod pogrešan", false);
    run(&a,&b,&c,Tamper::BadD, "[negativan] |D|[3]+1 (anchor puca)", false);
    run(&a,&b,&c,Tamper::BreakLink, "[negativan] perm PVAL pokvaren (mult↔anchor)", false);
    println!("\nSVE PROSLO: |D|←a,b,c na L=64, sliding-window mult, {} kolona < 255.", MAIN_W+AUX_W);
}
