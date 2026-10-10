// PRAVI multi-limb × multi-limb segment: dokazuje  A · B = C  (za a·c u anchoru).
// A,B su La=Lb=8 limba od 16 bita (128-bit svaki), C do 16 limba (256-bit).
//
// KLJUCNO ZA ZVUCNOST (bounded akumulator):
//   16-bit limbovi -> svaki proizvod A[i]·B[j] < 2^32.
//   Po poziciji k sabira se do min(La,Lb)=8 proizvoda + carry:
//     s_k = cin + Σ_{i+j=k} A[i]·B[j]  <  8·2^32 + 2^21  <  2^36  ≪  p=2^64.
//   Dakle NEMA wrap-around mod p — akumulacija vise proizvoda je zvucna.
//   Carry naraste do ~2^20 (NE 16-bit!) -> range-check na 21 bit.
//
// Layout: A,B broadcast kao KONSTANTNE kolone; jedna izlazna pozicija po redu;
// konvolucija preko one-hot pozicionog selektora POS (POS[k]=1 na redu k).
//   conv = Σ_{i,j} POS[i+j]·A[i]·B[j]   (stepen 3)

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, matrix::ColMatrix, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const LB: usize = 16;
const RADIX: u64 = 1 << LB;
const LA: usize = 8;
const LBN: usize = 8;              // limba u B
const NPOS: usize = 16;            // izlaznih pozicija (0..15) = LA+LBN
const N: usize = 32;              // duzina traga (pow2)
const CBW: usize = 16;            // bitova za C limb
const NBW: usize = 21;            // bitova za carry (do 2^20 < 2^21)

// kolone
const A0: usize = 0;
const B0: usize = A0 + LA;
const POS0: usize = B0 + LBN;
const CIN: usize = POS0 + NPOS;
const C_COL: usize = CIN + 1;
const CBITS: usize = C_COL + 1;
const CNBITS: usize = CBITS + CBW;
const WIDTH: usize = CNBITS + NBW; // 8+8+16+1+1+16+21 = 71

#[derive(Clone)]
struct PubInputs { a: Vec<BaseElement>, b: Vec<BaseElement>, c: Vec<BaseElement> }
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone(); v.extend_from_slice(&self.b); v.extend_from_slice(&self.c); v
    }
}

struct MulAir { context: AirContext<BaseElement>, a: Vec<BaseElement>, b: Vec<BaseElement>, c: Vec<BaseElement> }

impl Air for MulAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(ti: TraceInfo, pi: PubInputs, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(3), // conv + carry (POS·A·B)
            TransitionConstraintDegree::new(1), // carry link
            TransitionConstraintDegree::new(1), // c recomposition
        ];
        for _ in 0..LA { d.push(TransitionConstraintDegree::new(1)); }   // A const
        for _ in 0..LBN { d.push(TransitionConstraintDegree::new(1)); }  // B const
        for _ in 0..NPOS { d.push(TransitionConstraintDegree::new(1)); } // POS shift
        for _ in 0..CBW { d.push(TransitionConstraintDegree::new(2)); }  // C bits bool
        for _ in 0..NBW { d.push(TransitionConstraintDegree::new(2)); }  // carry bits bool
        // granicni: cin0=0 ; A(8) ; B(8) ; POS one-hot row0 (16) ; C[0..NPOS] (16)
        let n_assert = 1 + LA + LBN + NPOS + NPOS;
        let context = AirContext::new(ti, d, n_assert, options);
        MulAir { context, a: pi.a, b: pi.b, c: pi.c }
    }

    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));

        // rekonstrukcije iz bitova
        let mut cnext = E::ZERO;
        let mut crec = E::ZERO;
        for k in 0..CBW { crec += cur[CBITS + k] * E::from(BaseElement::new(1u64 << k)); }
        for k in 0..NBW { cnext += cur[CNBITS + k] * E::from(BaseElement::new(1u64 << k)); }

        // konvolucija: conv = Σ_{i,j} POS[i+j]·A[i]·B[j]
        let mut conv = E::ZERO;
        for i in 0..LA {
            for j in 0..LBN {
                conv += cur[POS0 + i + j] * cur[A0 + i] * cur[B0 + j];
            }
        }

        let mut r = 0;
        // 1) cin + conv == c + RADIX·cnext
        result[r] = cur[CIN] + conv - (cur[C_COL] + radix * cnext); r += 1;
        // 2) carry lanac
        result[r] = nxt[CIN] - cnext; r += 1;
        // 3) c iz bitova
        result[r] = cur[C_COL] - crec; r += 1;
        // 4) A konstantno
        for i in 0..LA { result[r] = nxt[A0 + i] - cur[A0 + i]; r += 1; }
        // 5) B konstantno
        for j in 0..LBN { result[r] = nxt[B0 + j] - cur[B0 + j]; r += 1; }
        // 6) POS shift: nxt.POS[0]=0 ; nxt.POS[k]=cur.POS[k-1]
        result[r] = nxt[POS0] - E::ZERO; r += 1;
        for k in 1..NPOS { result[r] = nxt[POS0 + k] - cur[POS0 + k - 1]; r += 1; }
        // 7) C bits boolean
        for k in 0..CBW { result[r] = cur[CBITS + k] * (cur[CBITS + k] - one); r += 1; }
        // 8) carry bits boolean
        for k in 0..NBW { result[r] = cur[CNBITS + k] * (cur[CNBITS + k] - one); r += 1; }
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(CIN, 0, BaseElement::ZERO));
        for i in 0..LA { v.push(Assertion::single(A0 + i, 0, self.a[i])); }
        for j in 0..LBN { v.push(Assertion::single(B0 + j, 0, self.b[j])); }
        v.push(Assertion::single(POS0, 0, BaseElement::ONE));
        for k in 1..NPOS { v.push(Assertion::single(POS0 + k, 0, BaseElement::ZERO)); }
        for k in 0..NPOS { v.push(Assertion::single(C_COL, k, self.c[k])); }
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> {
    (0..n).map(|k| BaseElement::new((x >> k) & 1)).collect()
}

fn build_rows(a: &[u64], b: &[u64]) -> (Vec<[BaseElement; WIDTH]>, Vec<u64>) {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    let mut c_out = vec![0u64; NPOS];
    let mut cin: u64 = 0;
    for k in 0..N {
        // konvolucija za poziciju k
        let mut conv: u64 = 0;
        if k < NPOS {
            for i in 0..LA {
                if k >= i && k - i < LBN { conv += a[i] * b[k - i]; }
            }
        }
        let s = conv + cin;
        let ci = s % RADIX;
        let cnext = s / RADIX;
        if k < NPOS { c_out[k] = ci; }
        let mut row = [BaseElement::ZERO; WIDTH];
        for i in 0..LA { row[A0 + i] = BaseElement::new(a[i]); }
        for j in 0..LBN { row[B0 + j] = BaseElement::new(b[j]); }
        if k < NPOS { row[POS0 + k] = BaseElement::ONE; }
        row[CIN] = BaseElement::new(cin);
        row[C_COL] = BaseElement::new(ci);
        let cb = bits(ci, CBW); let nb = bits(cnext, NBW);
        for t in 0..CBW { row[CBITS + t] = cb[t]; }
        for t in 0..NBW { row[CNBITS + t] = nb[t]; }
        rows[k] = row;
        cin = cnext;
    }
    (rows, c_out)
}

fn build_trace(rows: &[[BaseElement; WIDTH]]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    let r0 = rows[0];
    let owned = rows.to_vec();
    t.fill(
        |s| { for j in 0..WIDTH { s[j] = r0[j]; } },
        |step, s| { let nr = owned[step + 1]; for j in 0..WIDTH { s[j] = nr[j]; } },
    );
    t
}

struct P { options: ProofOptions, pi: PubInputs }
impl Prover for P {
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
fn tb(v: &[u64]) -> Vec<BaseElement> { v.iter().map(|&x| BaseElement::new(x)).collect() }

fn ref_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; NPOS];
    let mut cin: u128 = 0;
    for k in 0..NPOS {
        let mut s: u128 = cin;
        for i in 0..LA {
            if k >= i && k - i < LBN { s += a[i] as u128 * b[k - i] as u128; }
        }
        out[k] = (s % RADIX as u128) as u64;
        cin = s / RADIX as u128;
    }
    assert_eq!(cin, 0, "proizvod prelazi NPOS limba");
    out
}

fn main() {
    let a: Vec<u64> = vec![0xABCD, 0x1234, 0xFFFF, 0x0001, 0x8000, 0x7FFF, 0xDEAD, 0xBEEF];
    let b: Vec<u64> = vec![0x1357, 0x2468, 0xACE0, 0xFDB9, 0x0F0F, 0xF0F0, 0x00FF, 0xFF00];
    let (rows, c) = build_rows(&a, &b);
    let expected = ref_mul(&a, &b);
    assert_eq!(expected, c, "C != A*B (build bug)");

    println!("== PRAVI multi-limb × multi-limb: A · B = C ==");
    println!("A = {} limba, B = {} limba (16-bit svaki)", LA, LBN);
    println!("C = {} limba: {:?}", NPOS, c);
    // max akumulator izmeren tokom build-a
    let mut max_s: u64 = 0; let mut max_carry: u64 = 0; let mut cin = 0u64;
    for k in 0..N {
        let mut conv = 0u64;
        if k < NPOS { for i in 0..LA { if k>=i && k-i<LBN { conv += a[i]*b[k-i]; } } }
        let s = conv + cin; max_s = max_s.max(s); max_carry = max_carry.max(s/RADIX); cin = s/RADIX;
    }
    println!("[ok] referentna multiplikacija se poklapa sa C");
    println!("max akumulator s = {} (~2^{:.1}) ; max carry = {} (~2^{:.1}) ; p ~ 2^64",
             max_s, (max_s as f64).log2(), max_carry, (max_carry as f64).log2());

    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let pi = PubInputs { a: tb(&a), b: tb(&b), c: tb(&c) };
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&rows);

    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove failed");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes();
    let sec = proof.security_level::<H>(true);
    println!("\n== DOKAZ ==");
    println!("trace: {} redova x {} kolona (max deg 3)", N, WIDTH);
    println!("velicina dokaza : {} B ({:.1} KB)", pb.len(), pb.len() as f64 / 1024.0);
    println!("dokazivanje     : {:.1} ms ; sigurnost(conj) {} bita", prove_ms, sec);

    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<MulAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!("\n== VERIFIKACIJA ==");
    println!("[{}] validan dokaz za {:.2} ms", if ok { "PASS" } else { "FAIL" }, verify_ms);
    if !ok { std::process::exit(1); }

    println!("\n== NEGATIVNI TESTOVI ==");
    let mut c1 = c.clone(); c1[5] ^= 1;
    let r1 = winterfell::verify::<MulAir, H, RC>(proof.clone(), PubInputs { c: tb(&c1), ..pi.clone() }, &mo);
    println!("lazno C                : {}", if r1.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    let mut a1 = pi.a.clone(); a1[2] = a1[2] + BaseElement::ONE;
    let r2 = winterfell::verify::<MulAir, H, RC>(proof.clone(), PubInputs { a: a1, ..pi.clone() }, &mo);
    println!("lazno A                : {}", if r2.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    let mut b1 = pi.b.clone(); b1[4] = b1[4] + BaseElement::ONE;
    let r3 = winterfell::verify::<MulAir, H, RC>(proof.clone(), PubInputs { b: b1, ..pi.clone() }, &mo);
    println!("lazno B                : {}", if r3.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    let mut t = pb.clone(); let m = t.len() / 2; t[m] ^= 0x01;
    let r4 = winterfell::StarkProof::from_bytes(&t).map_err(|_| ())
        .and_then(|p| winterfell::verify::<MulAir, H, RC>(p, pi.clone(), &mo).map_err(|_| ()));
    println!("ostecen dokaz          : {}", if r4.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });

    if !(r1.is_err() && r2.is_err() && r3.is_err() && r4.is_err()) {
        println!("\nNEGATIVAN TEST PAO!"); std::process::exit(2);
    }
    println!("\nSVE PROSLO: multi-limb proizvod dokazan, bounded akumulator zvucan.");
}
