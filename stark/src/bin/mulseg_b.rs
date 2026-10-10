// MILESTONE B: pun 64×64 multi-limb mnozilac  a · c = C  (za a·c i b²).
// a,c = 64 limba x 16 bita (1024-bit) -> C = 128 limba (2048-bit).
//
// PROBLEM: naivni mulseg2 (A:64 broadcast + C:64 + POS:128 one-hot) = 256 kolona
// samo operandi+POS -> PROBIJA 255.
// RESENJE: SLIDING-WINDOW umesto POS one-hot.
//   conv_k = Σ_{i} a_i·c_{k-i}.  A je stacionaran (64 broadcast),
//   c KLIZI kroz prozor CW (64):  CW[i] = c_{k-i}, prozor se pomera svaki red.
//   conv = Σ_i A[i]·CW[i]  (degree 2, bez 127 POS kolona).
// Budzet: A(64)+CW(64)+CIN+C+CBITS(16)+CNBITS(23) = 169 kolona < 255.

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
const L: usize = 64;             // limba u a i c
const N: usize = 128;           // izlaznih pozicija = 2L; C ima 2L=128 limba
const CBW: usize = 16;
const NBW: usize = 23;          // carry do ~2^22

const AW: usize = 0;                 // A broadcast (64)
const CW: usize = AW + L;            // sliding window (64)
const CIN: usize = CW + L;
const C_COL: usize = CIN + 1;
const CBITS: usize = C_COL + 1;
const CNBITS: usize = CBITS + CBW;
const WIDTH: usize = CNBITS + NBW;   // 64+64+1+1+16+23 = 169

#[derive(Clone)]
struct Pub { a: Vec<BaseElement>, c: Vec<BaseElement>, prod: Vec<BaseElement> }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone(); v.extend_from_slice(&self.c); v.extend_from_slice(&self.prod); v
    }
}

struct MulAir { context: AirContext<BaseElement>, a: Vec<BaseElement>, c: Vec<BaseElement>, prod: Vec<BaseElement> }
impl Air for MulAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, pi: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(2), // conv + carry
            TransitionConstraintDegree::new(1), // carry link
            TransitionConstraintDegree::new(1), // c recomposition
        ];
        for _ in 0..L { d.push(TransitionConstraintDegree::new(1)); }       // A const
        for _ in 1..L { d.push(TransitionConstraintDegree::new(1)); }       // window shift
        for _ in 0..CBW { d.push(TransitionConstraintDegree::new(2)); }     // C bits
        for _ in 0..NBW { d.push(TransitionConstraintDegree::new(2)); }     // carry bits
        // asertacije: cin0 ; A(L) ; CW[0] po redu (N) ; CW[1..L] row0 =0 ; C(N)
        let n_assert = 1 + L + N + (L - 1) + N;
        MulAir { context: AirContext::new(ti, d, n_assert, options), a: pi.a, c: pi.c, prod: pi.prod }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX));
        let mut cnext = E::ZERO; let mut crec = E::ZERO;
        for k in 0..CBW { crec += cur[CBITS + k] * E::from(BaseElement::new(1u64 << k)); }
        for k in 0..NBW { cnext += cur[CNBITS + k] * E::from(BaseElement::new(1u64 << k)); }
        // conv = Σ A[i]·CW[i]
        let mut conv = E::ZERO;
        for i in 0..L { conv += cur[AW + i] * cur[CW + i]; }
        let mut r = 0;
        result[r] = conv + cur[CIN] - (cur[C_COL] + radix * cnext); r += 1;  // conv+carry
        result[r] = nxt[CIN] - cnext; r += 1;                                // carry link
        result[r] = cur[C_COL] - crec; r += 1;                               // c recomp
        for i in 0..L { result[r] = nxt[AW + i] - cur[AW + i]; r += 1; }      // A const
        for i in 1..L { result[r] = nxt[CW + i] - cur[CW + i - 1]; r += 1; }  // window shift
        for k in 0..CBW { result[r] = cur[CBITS + k] * (cur[CBITS + k] - one); r += 1; }
        for k in 0..NBW { result[r] = cur[CNBITS + k] * (cur[CNBITS + k] - one); r += 1; }
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(CIN, 0, BaseElement::ZERO));
        for i in 0..L { v.push(Assertion::single(AW + i, 0, self.a[i])); }
        // CW[0] po redu = c[k] (k<L) inace 0
        for k in 0..N {
            let cv = if k < L { self.c[k] } else { BaseElement::ZERO };
            v.push(Assertion::single(CW, k, cv));
        }
        // prozor inicijalno prazan
        for i in 1..L { v.push(Assertion::single(CW + i, 0, BaseElement::ZERO)); }
        // rezultat
        for k in 0..N { v.push(Assertion::single(C_COL, k, self.prod[k])); }
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x >> k) & 1)).collect() }

fn build_rows(a: &[u64], c: &[u64]) -> (Vec<Vec<BaseElement>>, Vec<u64>) {
    let mut cols = vec![vec![BaseElement::ZERO; N]; WIDTH];
    let mut prod = vec![0u64; N];
    let mut cin = 0u64;
    for k in 0..N {
        // conv_k = Σ_i a_i·c_{k-i}
        let mut conv = 0u128;
        for i in 0..L { if k >= i && k - i < L { conv += a[i] as u128 * c[k - i] as u128; } }
        let acc = conv + cin as u128;
        let ci = (acc % RADIX as u128) as u64;
        let cnext = (acc / RADIX as u128) as u64;
        prod[k] = ci;
        for i in 0..L { cols[AW + i][k] = BaseElement::new(a[i]); }
        for i in 0..L { let idx = k as i64 - i as i64; cols[CW + i][k] = if idx >= 0 && (idx as usize) < L { BaseElement::new(c[idx as usize]) } else { BaseElement::ZERO }; }
        cols[CIN][k] = BaseElement::new(cin);
        cols[C_COL][k] = BaseElement::new(ci);
        let cb = bits(ci, CBW); let nb = bits(cnext, NBW);
        for t in 0..CBW { cols[CBITS + t][k] = cb[t]; }
        for t in 0..NBW { cols[CNBITS + t][k] = nb[t]; }
        cin = cnext;
    }
    (cols, prod)
}

fn build_trace(cols: &[Vec<BaseElement>]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    t.fill(|s| { for j in 0..WIDTH { s[j] = cols[j][0]; } },
           |step, s| { for j in 0..WIDTH { s[j] = cols[j][step + 1]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = MulAir; type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> Pub { self.pi.clone() }
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
fn ref_mul(a: &[u64], c: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; N]; let mut cin = 0u128;
    for k in 0..N {
        let mut s = cin;
        for i in 0..L { if k >= i && k - i < L { s += a[i] as u128 * c[k - i] as u128; } }
        out[k] = (s % RADIX as u128) as u64; cin = s / RADIX as u128;
    }
    assert_eq!(cin, 0); out
}

fn main() {
    let a: Vec<u64> = (0..L as u64).map(|i| (i * 40503 + 12345) % RADIX).collect();
    let c: Vec<u64> = (0..L as u64).map(|i| (i * 52237 + 7919) % RADIX).collect();
    let (cols, prod) = build_rows(&a, &c);
    assert_eq!(ref_mul(&a, &c), prod, "C != a*c");
    println!("== MILESTONE B: 64×64 multi-limb  a · c = C  (sliding-window) ==");
    println!("a,c = {} limba (1024-bit) -> C = {} limba (2048-bit)", L, N);
    println!("trag: {} redova x {} kolona  (POS one-hot izbegnut -> {} < 255)", N, WIDTH, WIDTH);

    let pi = Pub { a: tb(&a), c: tb(&c), prod: tb(&prod) };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&cols);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64() * 1000.0;
    println!("dokaz {:.1} KB ; prove {:.0} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64 / 1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    let mut pbad = prod.clone(); pbad[70] ^= 1;
    let r1 = winterfell::verify::<MulAir, H, RC>(proof.clone(), Pub { prod: tb(&pbad), ..pi.clone() }, &mo);
    println!("lazno C: {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let mut abad = pi.a.clone(); abad[20] = abad[20] + BaseElement::ONE;
    let r2 = winterfell::verify::<MulAir, H, RC>(proof.clone(), Pub { a: abad, ..pi.clone() }, &mo);
    println!("lazno a: {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: 64×64 mnozilac na punoj sirini, {} kolona < 255.", WIDTH);
}
