// MILESTONE E1: JEDNA PUNA rho normalize-izlaz vrednost, sklopljena iz primitiva
// na 2048-bit sirini. Racuna  B' = B + 2kA  (jezgro normalize/rho):
//   (1) P = 2k·A         -- single-limb mnozenje (mulseg_a obrazac)
//   (2) B' = B - P       -- potpisano oduzimanje (D2 primitiv, znak B')
//   (3) W = A - |B'| >= 0 -- normalizacioni opseg (|B'| <= A)
// Sve FUZIONISANO u jedan narrow-long trag (bez selektora, unutar-red protok kao D1).
// Prava un-normalizovana forma sa k=-3 (B=b+6a, P=6a, B'=b).
// c' = a - kb + k²c je ISTI obrazac sa vise clanova (single-limb mult + potpisani zbir).

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
const N: usize = 128;
const BW: usize = 16;
const PCW: usize = 4;    // P carry bits (2k·A[k] < 6·2^16 < 2^19 -> carry<2^3)

// narrow-long kolone
const Ac: usize = 0;      // A[k]
const Bc: usize = 1;      // B[k]
const Pc: usize = 2;      // P[k] = 2k·A[k] (+carry)
const PBITS: usize = 3;   // P[k] bitovi (16)
const PCBITS: usize = PBITS + BW; // P carry bitovi (4)
// potpisano oduzimanje B' = B - P
const BPc: usize = PCBITS + PCW;  // |B'[k]|
const SBP: usize = BPc + 1;       // sign B' (globalno)
const SBIN: usize = SBP + 1;      // sub borrow-in
const BPBITS: usize = SBIN + 1;   // |B'| bitovi (16)
const SBOUT: usize = BPBITS + BW; // sub carry-out bit
// normalizacija W = A - |B'|
const Wc: usize = SBOUT + 1;      // W[k]
const WBIN: usize = Wc + 1;       // W borrow-in
const WBITS: usize = WBIN + 1;    // W bitovi (16)
const WBOUT: usize = WBITS + BW;  // W carry-out bit
const WIDTH: usize = WBOUT + 1;   // ~ 43

#[derive(Clone)]
struct Pub { a: Vec<BaseElement>, b: Vec<BaseElement>, p: Vec<BaseElement>, bp: Vec<BaseElement>, w: Vec<BaseElement>, twok: BaseElement, sbp: BaseElement }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone();
        for x in [&self.b, &self.p, &self.bp, &self.w] { v.extend_from_slice(x); }
        v.push(self.twok); v.push(self.sbp); v
    }
}

struct E1Air { context: AirContext<BaseElement>, p: Pub }
impl Air for E1Air {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(1), // P = 2k·A + carry   (2k je javna konstanta -> deg 1)
            TransitionConstraintDegree::new(1), // P carry link
            TransitionConstraintDegree::new(1), // P recomp
            TransitionConstraintDegree::new(1), // sub: small+|Z|+bin == big+R·bout  (znak B' global)
            TransitionConstraintDegree::new(1), // sub borrow link
            TransitionConstraintDegree::new(1), // B' recomp
            TransitionConstraintDegree::new(1), // sign B' konstanta
            TransitionConstraintDegree::new(2), // sign B' bool
            TransitionConstraintDegree::new(1), // W: |B'| + W + wbin == A + R·wbout
            TransitionConstraintDegree::new(1), // W borrow link
            TransitionConstraintDegree::new(1), // W recomp
        ];
        for _ in 0..BW { d.push(TransitionConstraintDegree::new(2)); }  // P bits
        for _ in 0..PCW { d.push(TransitionConstraintDegree::new(2)); } // P carry bits
        for _ in 0..BW { d.push(TransitionConstraintDegree::new(2)); }  // B' bits
        d.push(TransitionConstraintDegree::new(2));                     // sub bout bool
        for _ in 0..BW { d.push(TransitionConstraintDegree::new(2)); }  // W bits
        d.push(TransitionConstraintDegree::new(2));                     // W bout bool
        // asertacije: pcin0(P carry via bits, pa cin=0 preko borrow) -- koristimo bin0,wbin0,pcin0
        //   SBIN0=0, WBIN0=0, P-carry0=0(preko prvog reda) ; A,B,P,BP,W po redu (5N) ; SBP row0
        let n_assert = 3 + 5 * N + 1;
        E1Air { context: AirContext::new(ti, d, n_assert, options), p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX));
        let twok = E::from(self.p.twok);
        // rekonstrukcije
        let mut prec = E::ZERO; let mut pcarry = E::ZERO;
        for k in 0..BW { prec += cur[PBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        for k in 0..PCW { pcarry += cur[PCBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        let mut bprec = E::ZERO; for k in 0..BW { bprec += cur[BPBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        let mut wrec = E::ZERO; for k in 0..BW { wrec += cur[WBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        let sbp = cur[SBP];
        let mut r = 0;
        // (1) P = 2k·A[k] + pcin == Pc + R·pcout   (pcin u koloni PCARRY_COL, pcout iz PCBITS)
        result[r] = twok*cur[Ac] + cur[PCARRY_COL] - (cur[Pc] + radix*pcarry); r += 1;
        result[r] = nxt[PCARRY_COL] - pcarry; r += 1;   // P carry link
        result[r] = cur[Pc] - prec; r += 1;              // P recomp
        // (2) potpisano B' = B - P  (big=sbp?P:B, small=sbp?B:P)
        let big = sbp*cur[Pc] + (one-sbp)*cur[Bc];
        let small = sbp*cur[Bc] + (one-sbp)*cur[Pc];
        result[r] = small + cur[BPc] + cur[SBIN] - (big + radix*cur[SBOUT]); r += 1;
        result[r] = nxt[SBIN] - cur[SBOUT]; r += 1;
        result[r] = cur[BPc] - bprec; r += 1;
        result[r] = nxt[SBP] - cur[SBP]; r += 1;
        result[r] = sbp*(sbp-one); r += 1;
        // (3) normalizacija: |B'| + W + wbin == A + R·wbout   (W = A - |B'| >= 0)
        result[r] = cur[BPc] + cur[Wc] + cur[WBIN] - (cur[Ac] + radix*cur[WBOUT]); r += 1;
        result[r] = nxt[WBIN] - cur[WBOUT]; r += 1;
        result[r] = cur[Wc] - wrec; r += 1;
        // booleani
        for k in 0..BW { result[r] = cur[PBITS+k]*(cur[PBITS+k]-one); r += 1; }
        for k in 0..PCW { result[r] = cur[PCBITS+k]*(cur[PCBITS+k]-one); r += 1; }
        for k in 0..BW { result[r] = cur[BPBITS+k]*(cur[BPBITS+k]-one); r += 1; }
        result[r] = cur[SBOUT]*(cur[SBOUT]-one); r += 1;
        for k in 0..BW { result[r] = cur[WBITS+k]*(cur[WBITS+k]-one); r += 1; }
        result[r] = cur[WBOUT]*(cur[WBOUT]-one); r += 1;
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(SBIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(WBIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(PCARRY_COL, 0, BaseElement::ZERO));
        for k in 0..N {
            v.push(Assertion::single(Ac, k, self.p.a[k]));
            v.push(Assertion::single(Bc, k, self.p.b[k]));
            v.push(Assertion::single(Pc, k, self.p.p[k]));
            v.push(Assertion::single(BPc, k, self.p.bp[k]));
            v.push(Assertion::single(Wc, k, self.p.w[k]));
        }
        v.push(Assertion::single(SBP, 0, self.p.sbp));
        v
    }
}

// P carry-in se drzi u zasebnoj koloni PCARRY_COL.
const PCARRY_COL: usize = WBOUT + 1;

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x>>k)&1)).collect() }

fn build(a: &[u64], b: &[u64], p: &[u64], bp: &[u64], w: &[u64], twok: u64, sbp: u64) -> Vec<Vec<BaseElement>> {
    let mut col = vec![vec![BaseElement::ZERO; N]; WIDTH_FULL];
    let mut pcin = 0u64; let mut sbin = 0u64; let mut wbin = 0u64;
    for k in 0..N {
        // P = 2k·A[k] + pcin
        let pacc = twok * a[k] + pcin; let pk = pacc % RADIX; let pcout = pacc / RADIX;
        debug_assert_eq!(pk, p[k], "P limb {}", k);
        // sub big=small+|Z|
        let big = if sbp==1 { p[k] } else { b[k] };
        let small = if sbp==1 { b[k] } else { p[k] };
        let ss = small + bp[k] + sbin; let sbout = if ss>=RADIX {1} else {0};
        debug_assert_eq!(ss - sbout*RADIX, big, "sub limb {}", k);
        // W = A - |B'|  ->  |B'| + W + wbin == A + R·wbout
        let ws = bp[k] + w[k] + wbin; let wbout = if ws>=RADIX {1} else {0};
        debug_assert_eq!(ws - wbout*RADIX, a[k], "W limb {}", k);
        col[Ac][k]=BaseElement::new(a[k]); col[Bc][k]=BaseElement::new(b[k]);
        col[Pc][k]=BaseElement::new(pk); col[PCARRY_COL][k]=BaseElement::new(pcin);
        let pb=bits(pk,BW); for t in 0..BW { col[PBITS+t][k]=pb[t]; }
        let pcb=bits(pcout,PCW); for t in 0..PCW { col[PCBITS+t][k]=pcb[t]; }
        col[BPc][k]=BaseElement::new(bp[k]); col[SBP][k]=BaseElement::new(sbp);
        col[SBIN][k]=BaseElement::new(sbin); col[SBOUT][k]=BaseElement::new(sbout);
        let bpb=bits(bp[k],BW); for t in 0..BW { col[BPBITS+t][k]=bpb[t]; }
        col[Wc][k]=BaseElement::new(w[k]); col[WBIN][k]=BaseElement::new(wbin); col[WBOUT][k]=BaseElement::new(wbout);
        let wb=bits(w[k],BW); for t in 0..BW { col[WBITS+t][k]=wb[t]; }
        pcin=pcout; sbin=sbout; wbin=wbout;
    }
    col
}
const WIDTH_FULL: usize = PCARRY_COL + 1;
fn build_trace(col: &[Vec<BaseElement>]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH_FULL, N);
    t.fill(|s| { for j in 0..WIDTH_FULL { s[j]=col[j][0]; } },
           |step,s| { for j in 0..WIDTH_FULL { s[j]=col[j][step+1]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = E1Air; type Trace = TraceTable<BaseElement>;
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

fn main() {
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/norm.txt")).expect("norm.txt");
    let mut it = txt.lines();
    let pl = |s:&str| -> Vec<u64> { s.trim().split(',').map(|x| x.parse().unwrap()).collect() };
    let a=pl(it.next().unwrap()); let b=pl(it.next().unwrap()); let p=pl(it.next().unwrap());
    let bp=pl(it.next().unwrap()); let w=pl(it.next().unwrap());
    let last: Vec<u64> = it.next().unwrap().trim().split_whitespace().map(|x| x.parse().unwrap()).collect();
    let (twok, sbp) = (last[0], last[1]);
    let pad = |mut v: Vec<u64>| -> Vec<u64> { v.resize(N, 0); v };
    let (a, b, p, bp, w) = (pad(a), pad(b), pad(p), pad(bp), pad(w));
    let col = build(&a,&b,&p,&bp,&w,twok,sbp);
    println!("== MILESTONE E1: puna rho normalize-izlaz B'=B+2kA na 2048-bit ==");
    println!("sklopljeno: single-limb mult(P=2kA) + potpisano oduz(B'=B-P) + norm(A-|B'|>=0)");
    println!("trag: {} redova x {} kolona ; sve fuzionisano, bez selektora", N, WIDTH_FULL);

    let pi = Pub { a: tb(&a), b: tb(&b), p: tb(&p), bp: tb(&bp), w: tb(&w),
                   twok: BaseElement::new(twok), sbp: BaseElement::new(sbp) };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&col);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64()*1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<E1Air, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64()*1000.0;
    println!("dokaz {:.1} KB ; prove {:.0} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64/1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    let mut bpbad = bp.clone(); bpbad[20]^=1;
    let r1 = winterfell::verify::<E1Air, H, RC>(proof.clone(), Pub { bp: tb(&bpbad), ..pi.clone() }, &mo);
    println!("lazno B':  {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let mut wbad = w.clone(); wbad[0]=wbad[0].wrapping_add(1);
    let r2 = winterfell::verify::<E1Air, H, RC>(proof.clone(), Pub { w: tb(&wbad), ..pi.clone() }, &mo);
    println!("lazno W (norm): {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: puna normalize-izlaz vrednost sklopljena iz primitiva, {} kolona.", WIDTH_FULL);
}
