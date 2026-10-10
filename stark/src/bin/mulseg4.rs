// NORMALIZE/RHO segment: dokazuje LANAC rho rundi na PRAVOJ formi.
// Jedna rho runda: (a,b,c) -> (a',b',c') gde:
//   a' = c ;  b' = -b + 2k·c ;  c' = a - k·b + k²·c ;  uz  -a' < b' ≤ a'
// Nova mehanika koju prethodni segmenti nisu imali:
//   (1) ZNAK: b i k mogu biti negativni -> sign-magnitude reprezentacija.
//   (2) NORMALIZACIONI OPSEG: k jedinstveno pinovan uslovom -c < b' ≤ c,
//       preko dva NENEGATIVNA svedoka W1=c-b'≥0, W2=c+b'-1≥0.
//   (3) LANAC: red -> red je jedna rho runda (preview ulancavanja, stavka 5).
// Aritmetika je NATIVNA u polju (mali operandi < 2^30 -> svi medjurezultati
// < 2^35 ≪ p, bez preliva). Limb-nivo mnozenje za velike operande je mulseg2.
//
// NAPOMENA: range-check je bit-dekompozicija (5×30 + 6 kolona) -> ~150 kolona
// samo za opsege. To je direktna motivacija za LogUp (sledeci segment).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, matrix::ColMatrix, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const N: usize = 8;      // 8 formi = 7 rho tranzicija
const RB: usize = 30;    // range-bitovi za a,c,|b|,W1,W2
const KB: usize = 6;     // range-bitovi za |k|

// value kolone
const A: usize = 0;      // mag a (>0)
const C: usize = 1;      // mag c (>0)
const BM: usize = 2;     // mag |b|
const SB: usize = 3;     // sign b (0/1)
const KM: usize = 4;     // mag |k|
const SK: usize = 5;     // sign k
const W1: usize = 6;     // svedok c - b' (za NAREDNI b)
const W2: usize = 7;     // svedok c + b' - 1
// bit kolone
const ABITS: usize = 8;
const CBITS: usize = ABITS + RB;
const BBITS: usize = CBITS + RB;
const W1BITS: usize = BBITS + RB;
const W2BITS: usize = W1BITS + RB;
const KBITS: usize = W2BITS + RB;
const WIDTH: usize = KBITS + KB; // 8 + 5*30 + 6 = 164

#[derive(Clone)]
struct PubInputs {
    a0: BaseElement, c0: BaseElement, bm0: BaseElement, sb0: BaseElement,
    aN: BaseElement, cN: BaseElement, bmN: BaseElement, sbN: BaseElement,
}
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.a0, self.c0, self.bm0, self.sb0, self.aN, self.cN, self.bmN, self.sbN]
    }
}

struct RhoAir { context: AirContext<BaseElement>, pi: PubInputs }

fn signed<E: FieldElement>(mag: E, sign: E) -> E {
    // (1 - 2*sign) * mag
    (E::ONE - sign - sign) * mag
}

impl Air for RhoAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(ti: TraceInfo, pi: PubInputs, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(1), // a' = c
            TransitionConstraintDegree::new(3), // b' = -b + 2kc
            TransitionConstraintDegree::new(4), // c' = a - kb + k^2 c
            TransitionConstraintDegree::new(2), // W1 = c - b'
            TransitionConstraintDegree::new(2), // W2 = c + b' - 1
        ];
        // rekompozicije: A,C,BM,W1,W2,KM  (6)
        for _ in 0..6 { d.push(TransitionConstraintDegree::new(1)); }
        // sign booleani: SB, SK  (2)
        for _ in 0..2 { d.push(TransitionConstraintDegree::new(2)); }
        // bit booleani: 5*RB + KB
        for _ in 0..(5 * RB + KB) { d.push(TransitionConstraintDegree::new(2)); }
        // granicni: row0 (a,c,bm,sb) + rowN (a,c,bm,sb) = 8
        let context = AirContext::new(ti, d, 8, options);
        RhoAir { context, pi }
    }

    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let two = E::from(BaseElement::new(2));

        let sb = signed(cur[BM], cur[SB]);        // signed b
        let sk = signed(cur[KM], cur[SK]);        // signed k
        let sbp = signed(nxt[BM], nxt[SB]);       // signed b'
        let kk = cur[KM] * cur[KM];               // k^2 (sign nebitan)

        let mut r = 0;
        // 1) a' = c
        result[r] = nxt[A] - cur[C]; r += 1;
        // 2) b' = -b + 2kc
        result[r] = sbp - (E::ZERO - sb + two * sk * cur[C]); r += 1;
        // 3) c' = a - k*b + k^2*c
        result[r] = nxt[C] - (cur[A] - sk * sb + kk * cur[C]); r += 1;
        // 4) W1 = c - b'   (>=0, range-checked)
        result[r] = cur[W1] - (cur[C] - sbp); r += 1;
        // 5) W2 = c + b' - 1
        result[r] = cur[W2] - (cur[C] + sbp - one); r += 1;

        // rekompozicije iz bitova
        let recompose = |base: usize, n: usize| -> E {
            let mut acc = E::ZERO;
            for k in 0..n { acc += cur[base + k] * E::from(BaseElement::new(1u64 << k)); }
            acc
        };
        result[r] = cur[A]  - recompose(ABITS, RB);  r += 1;
        result[r] = cur[C]  - recompose(CBITS, RB);  r += 1;
        result[r] = cur[BM] - recompose(BBITS, RB);  r += 1;
        result[r] = cur[W1] - recompose(W1BITS, RB); r += 1;
        result[r] = cur[W2] - recompose(W2BITS, RB); r += 1;
        result[r] = cur[KM] - recompose(KBITS, KB);  r += 1;

        // sign booleani
        result[r] = cur[SB] * (cur[SB] - one); r += 1;
        result[r] = cur[SK] * (cur[SK] - one); r += 1;
        // bit booleani
        for base in [ABITS, CBITS, BBITS, W1BITS, W2BITS] {
            for k in 0..RB { result[r] = cur[base + k] * (cur[base + k] - one); r += 1; }
        }
        for k in 0..KB { result[r] = cur[KBITS + k] * (cur[KBITS + k] - one); r += 1; }
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = N - 1;
        vec![
            Assertion::single(A, 0, self.pi.a0),
            Assertion::single(C, 0, self.pi.c0),
            Assertion::single(BM, 0, self.pi.bm0),
            Assertion::single(SB, 0, self.pi.sb0),
            Assertion::single(A, last, self.pi.aN),
            Assertion::single(C, last, self.pi.cN),
            Assertion::single(BM, last, self.pi.bmN),
            Assertion::single(SB, last, self.pi.sbN),
        ]
    }
}

fn to_bits(x: i128, n: usize) -> Vec<BaseElement> {
    let x = x.unsigned_abs() as u64;
    (0..n).map(|k| BaseElement::new((x >> k) & 1)).collect()
}
fn fe(x: i128) -> BaseElement {
    // signed -> field (negativno = p - |x|)
    if x >= 0 { BaseElement::new(x as u64) }
    else { BaseElement::ZERO - BaseElement::new((-x) as u64) }
}
fn mag(x: i128) -> BaseElement { BaseElement::new(x.unsigned_abs() as u64) }
fn sgn(x: i128) -> BaseElement { if x < 0 { BaseElement::ONE } else { BaseElement::ZERO } }

fn build_trace(a: &[i128], b: &[i128], c: &[i128], k: &[i128]) -> TraceTable<BaseElement> {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    for i in 0..N {
        let ai = a[i]; let bi = b[i]; let ci = c[i];
        let ki = if i < N - 1 { k[i] } else { 0 };
        // W1,W2 za NAREDNI b (b[i+1]); za poslednji red nebitno (0)
        let (w1, w2) = if i < N - 1 {
            let bp = b[i + 1];
            (ci - bp, ci + bp - 1)
        } else { (0, 0) };
        let mut row = [BaseElement::ZERO; WIDTH];
        row[A] = mag(ai); row[C] = mag(ci);
        row[BM] = mag(bi); row[SB] = sgn(bi);
        row[KM] = mag(ki); row[SK] = sgn(ki);
        row[W1] = fe(w1); row[W2] = fe(w2);
        let ab = to_bits(ai, RB); let cb = to_bits(ci, RB); let bb = to_bits(bi, RB);
        let w1b = to_bits(w1, RB); let w2b = to_bits(w2, RB); let kb = to_bits(ki, KB);
        for t in 0..RB { row[ABITS+t]=ab[t]; row[CBITS+t]=cb[t]; row[BBITS+t]=bb[t];
                         row[W1BITS+t]=w1b[t]; row[W2BITS+t]=w2b[t]; }
        for t in 0..KB { row[KBITS+t]=kb[t]; }
        rows[i] = row;
    }
    let mut trace = TraceTable::new(WIDTH, N);
    let r0 = rows[0]; let owned = rows.clone();
    trace.fill(|s| { for j in 0..WIDTH { s[j]=r0[j]; } },
               |step, s| { let nr=owned[step+1]; for j in 0..WIDTH { s[j]=nr[j]; } });
    trace
}

struct P { options: ProofOptions, pi: PubInputs }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = RhoAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> PubInputs { self.pi.clone() }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self, ti: &TraceInfo, mt: &ColMatrix<BaseElement>, dom: &StarkDomain<BaseElement>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) { DefaultTraceLde::new(ti, mt, dom) }
    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self, air: &'a Self::Air, aux: winterfell::AuxTraceRandElements<E>,
        cc: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> { DefaultConstraintEvaluator::new(air, aux, cc) }
}

type H = Blake3_256<BaseElement>;
type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;

fn main() {
    // PRAVI lanac (256-bit... zapravo 36-bit D, generisan Pythonom), k=[-4,-9,-1,0,0,0,0]
    let a: Vec<i128> = vec![319749372, 21164782, 271736, 67927, 238134, 67927, 238134, 67927];
    let b: Vec<i128> = vec![-164528537, -4789719, -101529, -34325, 34325, -34325, 34325, -34325];
    let c: Vec<i128> = vec![21164782, 271736, 67927, 238134, 67927, 238134, 67927, 238134];
    let k: Vec<i128> = vec![-4, -9, -1, 0, 0, 0, 0];

    // sanity: rho jednacine na svakom koraku
    for i in 0..N-1 {
        assert_eq!(a[i+1], c[i]);
        assert_eq!(b[i+1], -b[i] + 2*k[i]*c[i]);
        assert_eq!(c[i+1], a[i] - k[i]*b[i] + k[i]*k[i]*c[i]);
        assert!(-c[i] < b[i+1] && b[i+1] <= c[i], "normalizacija pala na koraku {}", i);
    }
    println!("== NORMALIZE/RHO lanac: {} rundi na pravoj formi ==", N-1);
    println!("k niz = {:?}", k);
    println!("trag: {} redova x {} kolona (od cega ~{} range-check kolona -> motiv za LogUp)", N, WIDTH, 5*RB+KB);

    let pi = PubInputs {
        a0: mag(a[0]), c0: mag(c[0]), bm0: mag(b[0]), sb0: sgn(b[0]),
        aN: mag(a[N-1]), cN: mag(c[N-1]), bmN: mag(b[N-1]), sbN: sgn(b[N-1]),
    };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&a, &b, &c, &k);

    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove failed");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes();
    let sec = proof.security_level::<H>(true);
    println!("\n== DOKAZ ==");
    println!("velicina dokaza : {} B ({:.1} KB) ; prove {:.1} ms ; sec(conj) {} bita", pb.len(), pb.len() as f64/1024.0, prove_ms, sec);

    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<RhoAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!("[{}] validan dokaz za {:.2} ms", if ok {"PASS"} else {"FAIL"}, verify_ms);
    if !ok { std::process::exit(1); }

    println!("\n== NEGATIVNI TESTOVI ==");
    // 1) lazan pocetni b (menja ceo lanac -> rowN se ne poklapa / range pada)
    let r1 = winterfell::verify::<RhoAir, H, RC>(proof.clone(),
        PubInputs { bm0: mag(b[0]) + BaseElement::ONE, ..pi.clone() }, &mo);
    println!("lazan pocetni b        : {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    // 2) lazan finalni oblik
    let r2 = winterfell::verify::<RhoAir, H, RC>(proof.clone(),
        PubInputs { cN: mag(c[N-1]) + BaseElement::ONE, ..pi.clone() }, &mo);
    println!("lazan finalni c        : {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    // 3) ostecen dokaz
    let mut t = pb.clone(); let m = t.len()/2; t[m] ^= 0x01;
    let r3 = winterfell::StarkProof::from_bytes(&t).map_err(|_| ())
        .and_then(|p| winterfell::verify::<RhoAir, H, RC>(p, pi.clone(), &mo).map_err(|_| ()));
    println!("ostecen dokaz          : {}", if r3.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});

    if !(r1.is_err() && r2.is_err() && r3.is_err()) { println!("\nNEGATIVAN TEST PAO!"); std::process::exit(2); }
    println!("\nSVE PROSLO: rho lanac dokazan (znak + normalizacioni opseg + ulancavanje).");
}
