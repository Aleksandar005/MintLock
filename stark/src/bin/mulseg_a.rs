// MILESTONE A: pun 64-limb single-limb mnozilac  A · b = C.
// A = 64 limba x 16 bita (1024-bit), b = jedan 16-bit limb, C = 65 limba.
// Narrow-long: JEDAN limb po redu -> sirina ostaje ~konstantna (kao mulseg na 8
// limba), raste samo broj redova. Ovo kalibrise da li single-limb staza (k·c)
// staje udobno na punoj sirini (ocekivano DA).
// Range-check: bit-dekompozicija (u punoj montazi -> deljeni LogUp).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix, Air, AirContext, Assertion, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const LB: usize = 16;
const RADIX: u64 = 1 << LB;
const LA: usize = 64;            // limba u A (1024-bit)
const N: usize = 128;           // pow2 >= LA+1
const A_COL: usize = 0;
const CIN: usize = 1;
const C_COL: usize = 2;
const CBITS: usize = 3;
const CNBITS: usize = CBITS + LB;
const WIDTH: usize = CNBITS + LB;   // 3 + 16 + 16 = 35

#[derive(Clone)]
struct Pub { a: Vec<BaseElement>, b: BaseElement, c: Vec<BaseElement> }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone(); v.push(self.b); v.extend_from_slice(&self.c); v
    }
}

struct MulAir { context: AirContext<BaseElement>, a: Vec<BaseElement>, b: BaseElement, c: Vec<BaseElement> }
impl Air for MulAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, pi: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(1), // product/carry
            TransitionConstraintDegree::new(1), // carry link
            TransitionConstraintDegree::new(1), // c recomposition
        ];
        for _ in 0..LB { d.push(TransitionConstraintDegree::new(2)); } // c bits
        for _ in 0..LB { d.push(TransitionConstraintDegree::new(2)); } // cnext bits
        // asertacije: cin0=0 ; A[0..N] (svih N: realni + pad 0) ; C[0..=LA]
        let n_assert = 1 + N + (LA + 1);
        MulAir { context: AirContext::new(ti, d, n_assert, options), a: pi.a, b: pi.b, c: pi.c }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let b = E::from(self.b); let radix = E::from(BaseElement::new(RADIX));
        let mut cnext = E::ZERO; let mut crec = E::ZERO;
        for k in 0..LB {
            let p2 = E::from(BaseElement::new(1u64 << k));
            cnext += cur[CNBITS + k] * p2; crec += cur[CBITS + k] * p2;
        }
        result[0] = cur[A_COL] * b + cur[CIN] - (cur[C_COL] + radix * cnext);
        result[1] = nxt[CIN] - cnext;
        result[2] = cur[C_COL] - crec;
        for k in 0..LB { result[3 + k] = cur[CBITS + k] * (cur[CBITS + k] - one); }
        for k in 0..LB { result[3 + LB + k] = cur[CNBITS + k] * (cur[CNBITS + k] - one); }
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(CIN, 0, BaseElement::ZERO));
        for i in 0..N {
            let av = if i < LA { self.a[i] } else { BaseElement::ZERO };
            v.push(Assertion::single(A_COL, i, av));
        }
        for i in 0..=LA { v.push(Assertion::single(C_COL, i, self.c[i])); }
        v
    }
}

fn bits16(x: u64) -> [BaseElement; LB] {
    let mut o = [BaseElement::ZERO; LB];
    for k in 0..LB { o[k] = BaseElement::new((x >> k) & 1); }
    o
}
fn build_rows(a: &[u64], b: u64) -> (Vec<[BaseElement; WIDTH]>, Vec<u64>) {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    let mut c = vec![0u64; LA + 1];
    let mut cin = 0u64;
    for i in 0..N {
        let ai = if i < LA { a[i] } else { 0 };
        let acc = ai * b + cin; let ci = acc % RADIX; let cnext = acc / RADIX;
        if i <= LA { c[i] = ci; }
        let mut row = [BaseElement::ZERO; WIDTH];
        row[A_COL] = BaseElement::new(ai); row[CIN] = BaseElement::new(cin); row[C_COL] = BaseElement::new(ci);
        let cb = bits16(ci); let nb = bits16(cnext);
        for k in 0..LB { row[CBITS + k] = cb[k]; row[CNBITS + k] = nb[k]; }
        rows[i] = row; cin = cnext;
    }
    (rows, c)
}
fn build_trace(rows: &[[BaseElement; WIDTH]]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    let r0 = rows[0]; let owned = rows.to_vec();
    t.fill(|s| { for j in 0..WIDTH { s[j] = r0[j]; } },
           |step, s| { let nr = owned[step + 1]; for j in 0..WIDTH { s[j] = nr[j]; } });
    t
}

struct P { options: ProofOptions }
impl Prover for P {
    type BaseField = BaseElement; type Air = MulAir; type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let a = (0..LA).map(|i| t.get(A_COL, i)).collect();
        let c = (0..=LA).map(|i| t.get(C_COL, i)).collect();
        Pub { a, b: BaseElement::new(0xBEEF), c }
    }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self, ti: &TraceInfo, mt: &ColMatrix<BaseElement>, dom: &StarkDomain<BaseElement>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) { DefaultTraceLde::new(ti, mt, dom) }
    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self, air: &'a Self::Air, aux: winterfell::AuxTraceRandElements<E>,
        cc: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> { DefaultConstraintEvaluator::new(air, aux, cc) }
}
type H = Blake3_256<BaseElement>; type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;
fn tb(v: &[u64]) -> Vec<BaseElement> { v.iter().map(|&x| BaseElement::new(x)).collect() }
fn ref_mul(a: &[u64], b: u64) -> Vec<u64> {
    let mut out = vec![0u64; LA + 1]; let mut carry = 0u128;
    for i in 0..LA { let acc = a[i] as u128 * b as u128 + carry; out[i] = (acc & (RADIX as u128 - 1)) as u64; carry = acc >> LB; }
    out[LA] = carry as u64; out
}

fn main() {
    let a: Vec<u64> = (0..LA as u64).map(|i| (i * 40503 + 12345) % RADIX).collect();
    let b: u64 = 0xBEEF;
    let (rows, c) = build_rows(&a, b);
    assert_eq!(ref_mul(&a, b), c, "C != A*b");
    println!("== MILESTONE A: 64-limb single-limb  A · b = C ==");
    println!("A = {} limba (1024-bit) ; b = {:#06x} ; C = {} limba", LA, b, LA + 1);
    println!("trag: {} redova x {} kolona  (sirina KAO mulseg na 8 limba!)", N, WIDTH);

    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let pi = Pub { a: tb(&a), b: BaseElement::new(b), c: tb(&c) };
    let prover = P { options };
    let trace = build_trace(&rows);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64() * 1000.0;
    println!("dokaz {:.1} KB ; prove {:.1} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64 / 1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    // negativni
    let mut cbad = c.clone(); cbad[10] ^= 1;
    let r1 = winterfell::verify::<MulAir, H, RC>(proof.clone(), Pub { c: tb(&cbad), ..pi.clone() }, &mo);
    println!("lazno C: {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let mut abad = pi.a.clone(); abad[30] = abad[30] + BaseElement::ONE;
    let r2 = winterfell::verify::<MulAir, H, RC>(proof.clone(), Pub { a: abad, ..pi.clone() }, &mo);
    println!("lazno A: {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: 64-limb single-limb mnozilac, sirina {} (nezavisna od broja limba).", WIDTH);
}
