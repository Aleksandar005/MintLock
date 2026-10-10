// ANCHOR segment: dokazuje  4·(a·c) == b² + |D|  za PRAVU redukovanu formu.
// Produkte AC=a·c i BB=b² dokazuje mulseg2; ovaj segment izoluje NOVU mehaniku:
//   - mnozenje konstantom (×4) sa carry-jem
//   - sabiranje dva multi-limb broja (BB + |D|)
//   - jednakost 17-limbnih brojeva (per-limb L[k] == R_[k])
// Dve carry staze: LHS = 4·AC (do 2^18/limb), RHS = BB+|D|. Obe nenegativne
// (D<0 -> 4ac>b² -> |D|>0), pa je carry standardan, bez znaka.
//
// AC,BB,|D| su broadcast kao KONSTANTNE kolone; POS one-hot bira indeks k po redu.
// Ulazi su PRAVI (generisani iz prave forme, 256-bit D) -> identitet stvarno vazi.

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
const NOUT: usize = 18;   // izlaznih limba (17 realnih + pad)
const N: usize = 32;
const CBW: usize = 16;    // bitovi za izlazni limb
const LCW: usize = 3;     // bitovi za LHS carry (4·AC[k] < 2^18 -> carry < 2^2)
const RCW: usize = 2;     // bitovi za RHS carry (BB+D < 2^17 -> carry < 2^1)

const AC0: usize = 0;
const BB0: usize = AC0 + NOUT;
const D0: usize = BB0 + NOUT;
const POS0: usize = D0 + NOUT;
const LCIN: usize = POS0 + NOUT;
const L_COL: usize = LCIN + 1;
const LBITS: usize = L_COL + 1;
const LCBITS: usize = LBITS + CBW;
const RCIN: usize = LCBITS + LCW;
const R_COL: usize = RCIN + 1;
const RBITS: usize = R_COL + 1;
const RCBITS: usize = RBITS + CBW;
const WIDTH: usize = RCBITS + RCW; // 54 + 18 + 21 + 20 = 113

#[derive(Clone)]
struct PubInputs { ac: Vec<BaseElement>, bb: Vec<BaseElement>, d: Vec<BaseElement> }
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.ac.clone(); v.extend_from_slice(&self.bb); v.extend_from_slice(&self.d); v
    }
}

struct AnchorAir { context: AirContext<BaseElement>, ac: Vec<BaseElement>, bb: Vec<BaseElement>, d: Vec<BaseElement> }

impl Air for AnchorAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(ti: TraceInfo, pi: PubInputs, options: ProofOptions) -> Self {
        let mut deg = vec![
            TransitionConstraintDegree::new(2), // LHS 4·AC_k (+carry)
            TransitionConstraintDegree::new(2), // RHS BB_k+D_k (+carry)
            TransitionConstraintDegree::new(1), // lcarry link
            TransitionConstraintDegree::new(1), // rcarry link
            TransitionConstraintDegree::new(1), // ANCHOR: L == R_
            TransitionConstraintDegree::new(1), // L recomp
            TransitionConstraintDegree::new(1), // R_ recomp
        ];
        for _ in 0..NOUT { deg.push(TransitionConstraintDegree::new(1)); } // POS shift
        for _ in 0..(3 * NOUT) { deg.push(TransitionConstraintDegree::new(1)); } // AC/BB/D const
        for _ in 0..CBW { deg.push(TransitionConstraintDegree::new(2)); } // L bits
        for _ in 0..LCW { deg.push(TransitionConstraintDegree::new(2)); } // lcarry bits
        for _ in 0..CBW { deg.push(TransitionConstraintDegree::new(2)); } // R bits
        for _ in 0..RCW { deg.push(TransitionConstraintDegree::new(2)); } // rcarry bits
        // granicni
        let n_assert = 2 + NOUT + 3 * NOUT; // lcin0,rcin0 ; POS row0 (NOUT) ; AC/BB/D row0 (3·NOUT)
        let context = AirContext::new(ti, deg, n_assert, options);
        AnchorAir { context, ac: pi.ac, bb: pi.bb, d: pi.d }
    }

    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));

        // POS-selektovani limbi
        let mut ac_k = E::ZERO; let mut bb_k = E::ZERO; let mut d_k = E::ZERO;
        for m in 0..NOUT {
            ac_k += cur[POS0 + m] * cur[AC0 + m];
            bb_k += cur[POS0 + m] * cur[BB0 + m];
            d_k  += cur[POS0 + m] * cur[D0 + m];
        }
        // rekonstrukcije carry-ja iz bitova
        let mut lcarry = E::ZERO; let mut rcarry = E::ZERO;
        let mut lrec = E::ZERO; let mut rrec = E::ZERO;
        for k in 0..CBW {
            let p2 = E::from(BaseElement::new(1u64 << k));
            lrec += cur[LBITS + k] * p2;
            rrec += cur[RBITS + k] * p2;
        }
        for k in 0..LCW { lcarry += cur[LCBITS + k] * E::from(BaseElement::new(1u64 << k)); }
        for k in 0..RCW { rcarry += cur[RCBITS + k] * E::from(BaseElement::new(1u64 << k)); }

        let mut r = 0;
        // 1) LHS: 4·AC_k + lcin == L + RADIX·lcarry
        result[r] = four * ac_k + cur[LCIN] - (cur[L_COL] + radix * lcarry); r += 1;
        // 2) RHS: BB_k + D_k + rcin == R_ + RADIX·rcarry
        result[r] = bb_k + d_k + cur[RCIN] - (cur[R_COL] + radix * rcarry); r += 1;
        // 3,4) carry lanci
        result[r] = nxt[LCIN] - lcarry; r += 1;
        result[r] = nxt[RCIN] - rcarry; r += 1;
        // 5) ANCHOR: dve strane daju isti limb
        result[r] = cur[L_COL] - cur[R_COL]; r += 1;
        // 6,7) rekompozicija limba iz bitova
        result[r] = cur[L_COL] - lrec; r += 1;
        result[r] = cur[R_COL] - rrec; r += 1;
        // 8) POS shift
        result[r] = nxt[POS0] - E::ZERO; r += 1;
        for k in 1..NOUT { result[r] = nxt[POS0 + k] - cur[POS0 + k - 1]; r += 1; }
        // 9) AC/BB/D konstantno
        for m in 0..NOUT { result[r] = nxt[AC0 + m] - cur[AC0 + m]; r += 1; }
        for m in 0..NOUT { result[r] = nxt[BB0 + m] - cur[BB0 + m]; r += 1; }
        for m in 0..NOUT { result[r] = nxt[D0 + m] - cur[D0 + m]; r += 1; }
        // 10) bit booleani
        for k in 0..CBW { result[r] = cur[LBITS + k] * (cur[LBITS + k] - one); r += 1; }
        for k in 0..LCW { result[r] = cur[LCBITS + k] * (cur[LCBITS + k] - one); r += 1; }
        for k in 0..CBW { result[r] = cur[RBITS + k] * (cur[RBITS + k] - one); r += 1; }
        for k in 0..RCW { result[r] = cur[RCBITS + k] * (cur[RCBITS + k] - one); r += 1; }
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(LCIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(RCIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(POS0, 0, BaseElement::ONE));
        for k in 1..NOUT { v.push(Assertion::single(POS0 + k, 0, BaseElement::ZERO)); }
        for m in 0..NOUT { v.push(Assertion::single(AC0 + m, 0, self.ac[m])); }
        for m in 0..NOUT { v.push(Assertion::single(BB0 + m, 0, self.bb[m])); }
        for m in 0..NOUT { v.push(Assertion::single(D0 + m, 0, self.d[m])); }
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x >> k) & 1)).collect() }

fn build_rows(ac: &[u64], bb: &[u64], d: &[u64]) -> Vec<[BaseElement; WIDTH]> {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    let mut lcin = 0u64; let mut rcin = 0u64;
    for k in 0..N {
        let ack = if k < NOUT { ac[k] } else { 0 };
        let bbk = if k < NOUT { bb[k] } else { 0 };
        let dk  = if k < NOUT { d[k] } else { 0 };
        let ls = 4 * ack + lcin; let lc = ls / RADIX; let ll = ls % RADIX;
        let rs = bbk + dk + rcin; let rc = rs / RADIX; let rl = rs % RADIX;
        assert_eq!(ll, rl, "anchor ne balansira na limbu {}", k);
        let mut row = [BaseElement::ZERO; WIDTH];
        for m in 0..NOUT {
            row[AC0 + m] = BaseElement::new(ac[m]);
            row[BB0 + m] = BaseElement::new(bb[m]);
            row[D0 + m] = BaseElement::new(d[m]);
        }
        if k < NOUT { row[POS0 + k] = BaseElement::ONE; }
        row[LCIN] = BaseElement::new(lcin); row[L_COL] = BaseElement::new(ll);
        row[RCIN] = BaseElement::new(rcin); row[R_COL] = BaseElement::new(rl);
        let lb = bits(ll, CBW); let lcb = bits(lc, LCW);
        let rb = bits(rl, CBW); let rcb = bits(rc, RCW);
        for t in 0..CBW { row[LBITS + t] = lb[t]; row[RBITS + t] = rb[t]; }
        for t in 0..LCW { row[LCBITS + t] = lcb[t]; }
        for t in 0..RCW { row[RCBITS + t] = rcb[t]; }
        rows[k] = row;
        lcin = lc; rcin = rc;
    }
    rows
}

fn build_trace(rows: &[[BaseElement; WIDTH]]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    let r0 = rows[0]; let owned = rows.to_vec();
    t.fill(|s| { for j in 0..WIDTH { s[j] = r0[j]; } },
           |step, s| { let nr = owned[step + 1]; for j in 0..WIDTH { s[j] = nr[j]; } });
    t
}

struct P { options: ProofOptions, pi: PubInputs }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = AnchorAir;
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

fn main() {
    // PRAVI brojevi iz prave redukovane forme (256-bit D), generisani Pythonom:
    let ac: Vec<u64> = vec![34545,37925,64737,54582,44210,54984,59038,48610,46241,63678,51060,16882,25608,19833,37744,17094,0,0];
    let bb: Vec<u64> = vec![20257,9142,48534,4588,34226,43891,8364,27194,60077,21730,41518,38207,11155,14418,4427,4597,0,0];
    let d:  Vec<u64> = vec![52387,11487,13808,17135,11545,44975,31182,36177,59353,36375,31653,29323,25741,64915,15477,63781,0,0];

    let rows = build_rows(&ac, &bb, &d);
    println!("== ANCHOR: 4·(a·c) == b² + |D|  (prava forma, 256-bit D) ==");
    println!("AC,BB,|D|: {} limba (16-bit) ; trag {} redova x {} kolona (max deg 2)", NOUT, N, WIDTH);

    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let pi = PubInputs { ac: tb(&ac), bb: tb(&bb), d: tb(&d) };
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&rows);

    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove failed");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes();
    let sec = proof.security_level::<H>(true);
    println!("\n== DOKAZ ==");
    println!("velicina dokaza : {} B ({:.1} KB) ; prove {:.1} ms ; sec(conj) {} bita", pb.len(), pb.len() as f64/1024.0, prove_ms, sec);

    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!("[{}] validan dokaz za {:.2} ms", if ok { "PASS" } else { "FAIL" }, verify_ms);
    if !ok { std::process::exit(1); }

    println!("\n== NEGATIVNI TESTOVI ==");
    // 1) lazno |D| (perturbuj jedan limb) -> identitet pada
    let mut d1 = d.clone(); d1[7] ^= 1;
    let r1 = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), PubInputs { d: tb(&d1), ..pi.clone() }, &mo);
    println!("lazno |D|              : {}", if r1.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 2) lazno AC
    let mut a1 = ac.clone(); a1[3] ^= 1;
    let r2 = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), PubInputs { ac: tb(&a1), ..pi.clone() }, &mo);
    println!("lazno AC               : {}", if r2.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 3) lazno BB
    let mut b1 = bb.clone(); b1[10] ^= 1;
    let r3 = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), PubInputs { bb: tb(&b1), ..pi.clone() }, &mo);
    println!("lazno BB               : {}", if r3.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });
    // 4) ostecen dokaz
    let mut t = pb.clone(); let m = t.len()/2; t[m] ^= 0x01;
    let r4 = winterfell::StarkProof::from_bytes(&t).map_err(|_| ())
        .and_then(|p| winterfell::verify::<AnchorAir, H, RC>(p, pi.clone(), &mo).map_err(|_| ()));
    println!("ostecen dokaz          : {}", if r4.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });

    if !(r1.is_err() && r2.is_err() && r3.is_err() && r4.is_err()) { println!("\nNEGATIVAN TEST PAO!"); std::process::exit(2); }
    println!("\nSVE PROSLO: anchor 4ac=b²+|D| dokazan na pravoj formi, zvucnost potvrdjena.");
}
