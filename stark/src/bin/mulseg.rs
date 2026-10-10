// PRAVI (zvucan) MUL+CARRY segment: dokazuje  A * b = C  za bignum A (La limba
// od 16 bita) i JEDAN limb b (16 bita). To je tacno operacija koja dominira
// reduce (k*a, k*b, k^2*a — k je 1 limb). NIJE dummy stepen-2 lanac: pravi
// schoolbook carry lanac sa RANGE-CHECK-ovima (bit-dekompozicija), pa je
// falsifikovanje nemoguce. Negativni testovi to potvrdjuju.
//
// Zvucnost u polju: 16-bit limbovi -> A[i]*b < 2^32, acc < 2^32 << p, nema
// wrap-around mod p. C[i] i carry su 16-bit (bit-dekomponovani i boolean-vezani).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, matrix::ColMatrix, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain, Trace,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const LB: usize = 16;              // bita po limbu
const RADIX: u64 = 1 << LB;        // 65536
const LA: usize = 8;               // limba u A  (A je 128-bit)
const N: usize = 16;               // duzina traga (pow2, >= LA+1)

// kolone
const A_COL: usize = 0;
const CIN: usize = 1;
const C_COL: usize = 2;
const CBITS: usize = 3;            // 16 bitova C[i]
const CNBITS: usize = CBITS + LB;  // 16 bitova carry-next
const WIDTH: usize = CNBITS + LB;  // = 35

#[derive(Clone)]
struct PubInputs {
    a: Vec<BaseElement>,  // La limba
    b: BaseElement,       // 1 limb
    c: Vec<BaseElement>,  // La+1 limba
}
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone();
        v.push(self.b);
        v.extend_from_slice(&self.c);
        v
    }
}

struct MulAir {
    context: AirContext<BaseElement>,
    a: Vec<BaseElement>,
    b: BaseElement,
    c: Vec<BaseElement>,
}

impl Air for MulAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(trace_info: TraceInfo, pi: PubInputs, options: ProofOptions) -> Self {
        let mut degrees = vec![
            TransitionConstraintDegree::new(1), // product/carry
            TransitionConstraintDegree::new(1), // carry link nxt.cin == cnext
            TransitionConstraintDegree::new(1), // c recomposition
        ];
        for _ in 0..LB { degrees.push(TransitionConstraintDegree::new(2)); } // c bits boolean
        for _ in 0..LB { degrees.push(TransitionConstraintDegree::new(2)); } // cnext bits boolean
        // granicni: cin[0]=0 ; a[0..LA]=A ; a[LA..N]=0 ; c[0..=LA]=C
        let n_assert = 1 + LA + (N - LA) + (LA + 1);
        let context = AirContext::new(trace_info, degrees, n_assert, options);
        MulAir { context, a: pi.a, b: pi.b, c: pi.c }
    }

    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let b = E::from(self.b);
        let radix = E::from(BaseElement::new(RADIX));

        // rekonstrukcije iz bitova
        let mut cnext = E::ZERO;
        let mut crec = E::ZERO;
        for k in 0..LB {
            let p2 = E::from(BaseElement::new(1u64 << k));
            cnext += cur[CNBITS + k] * p2;
            crec += cur[CBITS + k] * p2;
        }

        // 1) acc = a*b + cin ; acc == c + RADIX*cnext
        result[0] = cur[A_COL] * b + cur[CIN] - (cur[C_COL] + radix * cnext);
        // 2) carry lanac: sledeci cin == cnext
        result[1] = nxt[CIN] - cnext;
        // 3) c iz svojih bitova
        result[2] = cur[C_COL] - crec;
        // 4) c bitovi boolean
        for k in 0..LB {
            result[3 + k] = cur[CBITS + k] * (cur[CBITS + k] - one);
        }
        // 5) cnext bitovi boolean
        for k in 0..LB {
            result[3 + LB + k] = cur[CNBITS + k] * (cur[CNBITS + k] - one);
        }
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut a = Vec::new();
        a.push(Assertion::single(CIN, 0, BaseElement::ZERO));
        for i in 0..LA {
            a.push(Assertion::single(A_COL, i, self.a[i]));
        }
        for i in LA..N {
            a.push(Assertion::single(A_COL, i, BaseElement::ZERO));
        }
        for i in 0..=LA {
            a.push(Assertion::single(C_COL, i, self.c[i]));
        }
        a
    }
}

fn bits16(x: u64) -> [BaseElement; LB] {
    let mut o = [BaseElement::ZERO; LB];
    for k in 0..LB { o[k] = BaseElement::new((x >> k) & 1); }
    o
}

// precompute svih N redova
fn build_rows(a: &[u64], b: u64) -> (Vec<[BaseElement; WIDTH]>, Vec<u64>) {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    let mut c_out = vec![0u64; LA + 1];
    let mut cin = 0u64;
    for i in 0..N {
        let ai = if i < LA { a[i] } else { 0 };
        let acc = ai * b + cin;
        let ci = acc % RADIX;
        let cnext = acc / RADIX;
        if i <= LA { c_out[i.min(LA)] = ci; }
        let mut row = [BaseElement::ZERO; WIDTH];
        row[A_COL] = BaseElement::new(ai);
        row[CIN] = BaseElement::new(cin);
        row[C_COL] = BaseElement::new(ci);
        let cb = bits16(ci); let nb = bits16(cnext);
        for k in 0..LB { row[CBITS + k] = cb[k]; row[CNBITS + k] = nb[k]; }
        rows[i] = row;
        cin = cnext;
    }
    (rows, c_out)
}

fn build_trace(rows: &[[BaseElement; WIDTH]]) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(WIDTH, N);
    let r0 = rows[0];
    let rows_owned: Vec<[BaseElement; WIDTH]> = rows.to_vec();
    trace.fill(
        |state| { for j in 0..WIDTH { state[j] = r0[j]; } },
        |step, state| {
            let nr = rows_owned[step + 1];
            for j in 0..WIDTH { state[j] = nr[j]; }
        },
    );
    trace
}

struct MulProver { options: ProofOptions, pi: PubInputs }
impl Prover for MulProver {
    type BaseField = BaseElement;
    type Air = MulAir;
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

fn to_be(v: &[u64]) -> Vec<BaseElement> { v.iter().map(|&x| BaseElement::new(x)).collect() }

fn main() {
    // realan primer: A (8x 16-bit limba) * b (16-bit)
    let a: Vec<u64> = vec![0xABCD, 0x1234, 0xFFFF, 0x0001, 0x8000, 0x7FFF, 0xDEAD, 0xBEEF];
    let b: u64 = 0xC0DE;

    let (rows, c) = build_rows(&a, b);

    // nezavisna provera: rekonstruisi velike brojeve i uporedi
    // nezavisna referentna schoolbook multiplikacija (bez preliva: per-poz < 2^36)
    let ref_mul = |a: &[u64], b: u64| -> Vec<u64> {
        let mut out = vec![0u64; a.len() + 1];
        let mut carry = 0u128;
        for i in 0..a.len() {
            let acc = a[i] as u128 * b as u128 + carry;
            out[i] = (acc & (RADIX as u128 - 1)) as u64;
            carry = acc >> LB;
        }
        out[a.len()] = carry as u64;
        out
    };
    let expected = ref_mul(&a, b);
    assert_eq!(expected, c, "C != A*b (build bug)");
    println!("== PRAVI MUL+CARRY segment: A * b = C ==");
    println!("A   = {} limba (16-bit): {:?}", LA, a);
    println!("b   = {:#06x}", b);
    println!("C   = {} limba: {:?}", LA + 1, c);
    println!("[ok] nezavisna referentna multiplikacija se poklapa sa C");

    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let pi = PubInputs { a: to_be(&a), b: BaseElement::new(b), c: to_be(&c) };
    let prover = MulProver { options, pi: pi.clone() };

    let trace = build_trace(&rows);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove failed");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes();
    let sec = proof.security_level::<H>(true);
    println!("\n== DOKAZ ==");
    println!("trace: {} redova x {} kolona ({} constraint, max deg 2)", N, WIDTH, 3 + 2 * LB);
    println!("velicina dokaza : {} B ({:.1} KB)", pb.len(), pb.len() as f64 / 1024.0);
    println!("dokazivanje     : {:.1} ms ; sigurnost(conj) {} bita", prove_ms, sec);

    let min_opts = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi.clone(), &min_opts).is_ok();
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!("\n== VERIFIKACIJA ==");
    println!("[{}] validan dokaz za {:.2} ms", if ok { "PASS" } else { "FAIL" }, verify_ms);
    if !ok { std::process::exit(1); }

    // ---- NEGATIVNI TESTOVI (zvucnost) ----
    println!("\n== NEGATIVNI TESTOVI ==");
    // 1) lazno C (flip jedan limb rezultata)
    let mut c_bad = c.clone(); c_bad[0] ^= 1;
    let pi_badc = PubInputs { c: to_be(&c_bad), ..pi.clone() };
    let r1 = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi_badc, &min_opts);
    println!("lazno C (flip bit)     : {}", if r1.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 2) lazno b (drugi mnozilac)
    let pi_badb = PubInputs { b: BaseElement::new(b ^ 1), ..pi.clone() };
    let r2 = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi_badb, &min_opts);
    println!("lazno b                : {}", if r2.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 3) lazno A
    let mut a_bad = pi.a.clone(); a_bad[3] = a_bad[3] + BaseElement::ONE;
    let pi_bada = PubInputs { a: a_bad, ..pi.clone() };
    let r3 = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi_bada, &min_opts);
    println!("lazno A                : {}", if r3.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 4) ostecen dokaz (flip bajt)
    let mut tb = pb.clone(); let m = tb.len() / 2; tb[m] ^= 0x01;
    let r4 = winterfell::StarkProof::from_bytes(&tb).map_err(|_| ())
        .and_then(|p| winterfell::verify::<MulAir, H, RC>(p, pi.clone(), &min_opts).map_err(|_| ()));
    println!("ostecen dokaz          : {}", if r4.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });

    let all_neg_ok = r1.is_err() && r2.is_err() && r3.is_err() && r4.is_err();
    if !all_neg_ok { println!("\nNEKI NEGATIVAN TEST NIJE PROSAO!"); std::process::exit(2); }
    println!("\nSVE PROSLO: pravi limb-proizvod dokazan i zvucnost potvrdjena.");
}
