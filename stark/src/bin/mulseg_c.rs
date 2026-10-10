// MILESTONE C: anchor  4·(a·c) == b² + |D|  na PUNOJ 2048-bit sirini.
// AC=a·c, BB=b² (svaki 128 limba = 2048-bit), |D| 128 limba. Prava forma.
//
// mulseg3 je koristio BROADCAST operande (AC+BB+D = 3*NL kolona) -> na 128 limba
// to je 384 kolone -> PROBIJA 255. Zato NARROW-LONG combine: AC,BB,D teku po
// jedan limb po redu (~44 kolone). Mnozioce a·c, b² pokriva mulseg_b (I/O).
//   LHS: 4·AC[k] + lcarry ; RHS: BB[k]+D[k]+rcarry ; ANCHOR: L[k]==R[k].
// Obe strane nenegativne (D<0 -> 4ac>b²) -> unsigned carry.

use std::time::Instant;
use std::fs;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix, Air, AirContext, Assertion, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const LB: usize = 16;
const RADIX: u64 = 1 << LB;
const N: usize = 128;    // izlaznih limba (2048-bit)
const CBW: usize = 16;
const LCW: usize = 3;    // LHS carry (4·AC[k] < 2^18 -> carry < 2^2)
const RCW: usize = 2;    // RHS carry (BB+D < 2^17 -> carry < 2^1)

// narrow-long kolone: po jedan limb AC,BB,D po redu
const ACc: usize = 0;    // AC[k]
const BBc: usize = 1;    // BB[k]
const Dc: usize = 2;     // D[k]
const LCIN: usize = 3;
const L_COL: usize = 4;
const LBITS: usize = 5;
const LCBITS: usize = LBITS + CBW;
const RCIN: usize = LCBITS + LCW;
const R_COL: usize = RCIN + 1;
const RBITS: usize = R_COL + 1;
const RCBITS: usize = RBITS + CBW;
const WIDTH: usize = RCBITS + RCW;   // 3+1+1+16+3+1+1+16+2 = 44

#[derive(Clone)]
struct Pub { ac: Vec<BaseElement>, bb: Vec<BaseElement>, d: Vec<BaseElement> }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.ac.clone(); v.extend_from_slice(&self.bb); v.extend_from_slice(&self.d); v
    }
}

struct AnchorAir { context: AirContext<BaseElement>, ac: Vec<BaseElement>, bb: Vec<BaseElement>, d: Vec<BaseElement> }
impl Air for AnchorAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, pi: Pub, options: ProofOptions) -> Self {
        let mut deg = vec![
            TransitionConstraintDegree::new(1), // LHS 4·AC + lcarry
            TransitionConstraintDegree::new(1), // RHS BB+D + rcarry
            TransitionConstraintDegree::new(1), // lcarry link
            TransitionConstraintDegree::new(1), // rcarry link
            TransitionConstraintDegree::new(1), // ANCHOR L==R
            TransitionConstraintDegree::new(1), // L recomp
            TransitionConstraintDegree::new(1), // R recomp
        ];
        for _ in 0..CBW { deg.push(TransitionConstraintDegree::new(2)); } // L bits
        for _ in 0..LCW { deg.push(TransitionConstraintDegree::new(2)); } // lcarry bits
        for _ in 0..CBW { deg.push(TransitionConstraintDegree::new(2)); } // R bits
        for _ in 0..RCW { deg.push(TransitionConstraintDegree::new(2)); } // rcarry bits
        // asertacije: lcin0,rcin0 ; AC,BB,D po redu (3*N)
        let n_assert = 2 + 3 * N;
        AnchorAir { context: AirContext::new(ti, deg, n_assert, options), ac: pi.ac, bb: pi.bb, d: pi.d }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));
        let mut lcarry = E::ZERO; let mut rcarry = E::ZERO;
        let mut lrec = E::ZERO; let mut rrec = E::ZERO;
        for k in 0..CBW { let p2 = E::from(BaseElement::new(1u64 << k)); lrec += cur[LBITS+k]*p2; rrec += cur[RBITS+k]*p2; }
        for k in 0..LCW { lcarry += cur[LCBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        for k in 0..RCW { rcarry += cur[RCBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        let mut r = 0;
        result[r] = four*cur[ACc] + cur[LCIN] - (cur[L_COL] + radix*lcarry); r += 1;   // LHS
        result[r] = cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_COL] + radix*rcarry); r += 1; // RHS
        result[r] = nxt[LCIN] - lcarry; r += 1;
        result[r] = nxt[RCIN] - rcarry; r += 1;
        result[r] = cur[L_COL] - cur[R_COL]; r += 1;   // ANCHOR
        result[r] = cur[L_COL] - lrec; r += 1;
        result[r] = cur[R_COL] - rrec; r += 1;
        for k in 0..CBW { result[r] = cur[LBITS+k]*(cur[LBITS+k]-one); r += 1; }
        for k in 0..LCW { result[r] = cur[LCBITS+k]*(cur[LCBITS+k]-one); r += 1; }
        for k in 0..CBW { result[r] = cur[RBITS+k]*(cur[RBITS+k]-one); r += 1; }
        for k in 0..RCW { result[r] = cur[RCBITS+k]*(cur[RCBITS+k]-one); r += 1; }
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(LCIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(RCIN, 0, BaseElement::ZERO));
        for k in 0..N {
            v.push(Assertion::single(ACc, k, self.ac[k]));
            v.push(Assertion::single(BBc, k, self.bb[k]));
            v.push(Assertion::single(Dc, k, self.d[k]));
        }
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x>>k)&1)).collect() }

fn build_cols(ac: &[u64], bb: &[u64], d: &[u64]) -> Vec<Vec<BaseElement>> {
    let mut col = vec![vec![BaseElement::ZERO; N]; WIDTH];
    let mut lcin = 0u64; let mut rcin = 0u64;
    for k in 0..N {
        let ls = 4*ac[k] + lcin; let lc = ls/RADIX; let ll = ls%RADIX;
        let rs = bb[k] + d[k] + rcin; let rc = rs/RADIX; let rl = rs%RADIX;
        assert_eq!(ll, rl, "anchor pao na limbu {}", k);
        col[ACc][k]=BaseElement::new(ac[k]); col[BBc][k]=BaseElement::new(bb[k]); col[Dc][k]=BaseElement::new(d[k]);
        col[LCIN][k]=BaseElement::new(lcin); col[L_COL][k]=BaseElement::new(ll);
        col[RCIN][k]=BaseElement::new(rcin); col[R_COL][k]=BaseElement::new(rl);
        let lb=bits(ll,CBW); let lcb=bits(lc,LCW); let rb=bits(rl,CBW); let rcb=bits(rc,RCW);
        for t in 0..CBW { col[LBITS+t][k]=lb[t]; col[RBITS+t][k]=rb[t]; }
        for t in 0..LCW { col[LCBITS+t][k]=lcb[t]; }
        for t in 0..RCW { col[RCBITS+t][k]=rcb[t]; }
        lcin=lc; rcin=rc;
    }
    col
}
fn build_trace(col: &[Vec<BaseElement>]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    t.fill(|s| { for j in 0..WIDTH { s[j]=col[j][0]; } },
           |step,s| { for j in 0..WIDTH { s[j]=col[j][step+1]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = AnchorAir; type Trace = TraceTable<BaseElement>;
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

fn read_limbs() -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/anchor128.txt")).expect("anchor128.txt");
    let mut it = txt.lines();
    let parse = |line: &str| -> Vec<u64> { line.trim().split(',').map(|x| x.parse().unwrap()).collect() };
    let ac = parse(it.next().unwrap()); let bb = parse(it.next().unwrap()); let d = parse(it.next().unwrap());
    (ac, bb, d)
}

fn main() {
    let (ac, bb, d) = read_limbs();
    assert_eq!(ac.len(), N); assert_eq!(bb.len(), N); assert_eq!(d.len(), N);
    let col = build_cols(&ac, &bb, &d);
    println!("== MILESTONE C: anchor 4ac=b²+|D| na 2048-bit (prava forma) ==");
    println!("AC,BB,|D|: {} limba (2048-bit) ; narrow-long combine", N);
    println!("trag: {} redova x {} kolona (broadcast izbegnut: 44 vs 384)", N, WIDTH);

    let pi = Pub { ac: tb(&ac), bb: tb(&bb), d: tb(&d) };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&col);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64()*1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64()*1000.0;
    println!("dokaz {:.1} KB ; prove {:.0} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64/1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    let mut dbad = d.clone(); dbad[64] ^= 1;
    let r1 = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), Pub { d: tb(&dbad), ..pi.clone() }, &mo);
    println!("lazno |D|: {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let mut acbad = ac.clone(); acbad[30] ^= 1;
    let r2 = winterfell::verify::<AnchorAir, H, RC>(proof.clone(), Pub { ac: tb(&acbad), ..pi.clone() }, &mo);
    println!("lazno AC:  {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: anchor na 2048-bit, {} kolona < 255.", WIDTH);
}
