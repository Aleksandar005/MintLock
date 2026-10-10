// MILESTONE D1: FUZIJA mnozilac(a·c) + anchor u JEDNOM tragu.
// Nalaz koji testiramo: fazni selektor NIJE potreban ako faze fuzionisemo preko
// GRUPA KOLONA (ne vremenski). Sliding-window mnozilac proizvodi AC[k] u redu k;
// anchor troshi AC[k] u ISTOM redu k -> protok podataka je UNUTAR-RED, bez
// cross-phase memorije i bez selektora.
//   mnozilac: conv=Σ A[i]·CW[i] -> AC[k] (=C_COL)
//   anchor:   4·AC[k] + lcarry == L ; BB[k]+D[k]+rcarry == R ; L==R
//   AC = deljena kolona (izlaz mnozioca = ulaz anchora).
// b² je zaseban segment (BB dolazi kao javni ulaz preko I/O).

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
const L: usize = 64;      // limba u a,c
const N: usize = 128;    // izlaznih limba AC (2048-bit)
const CBW: usize = 16;
const NBW: usize = 23;   // mnozilac carry
const LCW: usize = 3;    // anchor LHS carry
const RCW: usize = 2;    // anchor RHS carry

// --- mnozilac kolone ---
const AW: usize = 0;              // A broadcast (64)
const CW: usize = AW + L;         // sliding window (64)
const MCIN: usize = CW + L;       // mnozilac carry-in
const AC: usize = MCIN + 1;       // AC[k]  (DELJENO: izlaz mnozioca = ulaz anchora)
const CBITS: usize = AC + 1;
const CNBITS: usize = CBITS + CBW;
// --- anchor kolone ---
const BBc: usize = CNBITS + NBW;  // BB[k] (javni ulaz)
const Dc: usize = BBc + 1;        // D[k]  (javni ulaz)
const LCIN: usize = Dc + 1;
const L_COL: usize = LCIN + 1;
const LBITS: usize = L_COL + 1;
const LCBITS: usize = LBITS + CBW;
const RCIN: usize = LCBITS + LCW;
const R_COL: usize = RCIN + 1;
const RBITS: usize = R_COL + 1;
const RCBITS: usize = RBITS + CBW;
const WIDTH: usize = RCBITS + RCW;  // 64+64+1+1+16+23 + 1+1+1+1+16+3+1+1+16+2 = 212

#[derive(Clone)]
struct Pub { a: Vec<BaseElement>, c: Vec<BaseElement>, bb: Vec<BaseElement>, d: Vec<BaseElement>, ac: Vec<BaseElement> }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a.clone();
        for x in [&self.c, &self.bb, &self.d, &self.ac] { v.extend_from_slice(x); }
        v
    }
}

struct FuseAir { context: AirContext<BaseElement>, p: Pub }
impl Air for FuseAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(2), // mnozilac conv+carry
            TransitionConstraintDegree::new(1), // mnozilac carry link
            TransitionConstraintDegree::new(1), // AC recomp
        ];
        for _ in 0..L { d.push(TransitionConstraintDegree::new(1)); }   // A const
        for _ in 1..L { d.push(TransitionConstraintDegree::new(1)); }   // window shift
        for _ in 0..CBW { d.push(TransitionConstraintDegree::new(2)); } // AC bits
        for _ in 0..NBW { d.push(TransitionConstraintDegree::new(2)); } // mnozilac carry bits
        // anchor
        d.push(TransitionConstraintDegree::new(1)); // LHS 4·AC
        d.push(TransitionConstraintDegree::new(1)); // RHS
        d.push(TransitionConstraintDegree::new(1)); // lcarry link
        d.push(TransitionConstraintDegree::new(1)); // rcarry link
        d.push(TransitionConstraintDegree::new(1)); // ANCHOR L==R
        d.push(TransitionConstraintDegree::new(1)); // L recomp
        d.push(TransitionConstraintDegree::new(1)); // R recomp
        for _ in 0..CBW { d.push(TransitionConstraintDegree::new(2)); } // L bits
        for _ in 0..LCW { d.push(TransitionConstraintDegree::new(2)); } // lcarry bits
        for _ in 0..CBW { d.push(TransitionConstraintDegree::new(2)); } // R bits
        for _ in 0..RCW { d.push(TransitionConstraintDegree::new(2)); } // rcarry bits
        // asertacije: mcin0,lcin0,rcin0 ; A(L) ; CW[0] po redu (N) ; CW[1..L] row0 ; AC(N) ; BB(N) ; D(N)
        let n_assert = 3 + L + N + (L - 1) + N + N + N;
        FuseAir { context: AirContext::new(ti, d, n_assert, options), p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));
        // ---- mnozilac ----
        let mut cnext = E::ZERO; let mut crec = E::ZERO;
        for k in 0..CBW { crec += cur[CBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        for k in 0..NBW { cnext += cur[CNBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        let mut conv = E::ZERO;
        for i in 0..L { conv += cur[AW+i]*cur[CW+i]; }
        let mut r = 0;
        result[r] = conv + cur[MCIN] - (cur[AC] + radix*cnext); r += 1;
        result[r] = nxt[MCIN] - cnext; r += 1;
        result[r] = cur[AC] - crec; r += 1;
        for i in 0..L { result[r] = nxt[AW+i] - cur[AW+i]; r += 1; }
        for i in 1..L { result[r] = nxt[CW+i] - cur[CW+i-1]; r += 1; }
        for k in 0..CBW { result[r] = cur[CBITS+k]*(cur[CBITS+k]-one); r += 1; }
        for k in 0..NBW { result[r] = cur[CNBITS+k]*(cur[CNBITS+k]-one); r += 1; }
        // ---- anchor (AC = cur[AC], izlaz mnozioca u ISTOM redu) ----
        let mut lcarry = E::ZERO; let mut rcarry = E::ZERO;
        let mut lrec = E::ZERO; let mut rrec = E::ZERO;
        for k in 0..CBW { let p2=E::from(BaseElement::new(1u64<<k)); lrec+=cur[LBITS+k]*p2; rrec+=cur[RBITS+k]*p2; }
        for k in 0..LCW { lcarry += cur[LCBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        for k in 0..RCW { rcarry += cur[RCBITS+k]*E::from(BaseElement::new(1u64<<k)); }
        result[r] = four*cur[AC] + cur[LCIN] - (cur[L_COL] + radix*lcarry); r += 1;
        result[r] = cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_COL] + radix*rcarry); r += 1;
        result[r] = nxt[LCIN] - lcarry; r += 1;
        result[r] = nxt[RCIN] - rcarry; r += 1;
        result[r] = cur[L_COL] - cur[R_COL]; r += 1;     // ANCHOR
        result[r] = cur[L_COL] - lrec; r += 1;
        result[r] = cur[R_COL] - rrec; r += 1;
        for k in 0..CBW { result[r] = cur[LBITS+k]*(cur[LBITS+k]-one); r += 1; }
        for k in 0..LCW { result[r] = cur[LCBITS+k]*(cur[LCBITS+k]-one); r += 1; }
        for k in 0..CBW { result[r] = cur[RBITS+k]*(cur[RBITS+k]-one); r += 1; }
        for k in 0..RCW { result[r] = cur[RCBITS+k]*(cur[RCBITS+k]-one); r += 1; }
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(MCIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(LCIN, 0, BaseElement::ZERO));
        v.push(Assertion::single(RCIN, 0, BaseElement::ZERO));
        for i in 0..L { v.push(Assertion::single(AW+i, 0, self.p.a[i])); }
        for k in 0..N { let cv = if k<L { self.p.c[k] } else { BaseElement::ZERO }; v.push(Assertion::single(CW, k, cv)); }
        for i in 1..L { v.push(Assertion::single(CW+i, 0, BaseElement::ZERO)); }
        for k in 0..N { v.push(Assertion::single(AC, k, self.p.ac[k])); }
        for k in 0..N { v.push(Assertion::single(BBc, k, self.p.bb[k])); }
        for k in 0..N { v.push(Assertion::single(Dc, k, self.p.d[k])); }
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x>>k)&1)).collect() }

fn build(a: &[u64], c: &[u64], bb: &[u64], d: &[u64]) -> (Vec<Vec<BaseElement>>, Vec<u64>) {
    let mut col = vec![vec![BaseElement::ZERO; N]; WIDTH];
    let mut ac = vec![0u64; N];
    let mut mcin = 0u64; let mut lcin = 0u64; let mut rcin = 0u64;
    for k in 0..N {
        // mnozilac
        let mut conv = 0u128;
        for i in 0..L { if k>=i && k-i<L { conv += a[i] as u128 * c[k-i] as u128; } }
        let acc = conv + mcin as u128; let ack = (acc % RADIX as u128) as u64; let cnext = (acc / RADIX as u128) as u64;
        ac[k] = ack;
        for i in 0..L { col[AW+i][k] = BaseElement::new(a[i]); }
        for i in 0..L { let idx = k as i64 - i as i64; col[CW+i][k] = if idx>=0 && (idx as usize)<L { BaseElement::new(c[idx as usize]) } else { BaseElement::ZERO }; }
        col[MCIN][k] = BaseElement::new(mcin); col[AC][k] = BaseElement::new(ack);
        let cb = bits(ack, CBW); let nb = bits(cnext, NBW);
        for t in 0..CBW { col[CBITS+t][k]=cb[t]; } for t in 0..NBW { col[CNBITS+t][k]=nb[t]; }
        // anchor (koristi ack)
        let ls = 4*ack + lcin; let lc = ls/RADIX; let ll = ls%RADIX;
        let rs = bb[k] + d[k] + rcin; let rc = rs/RADIX; let rl = rs%RADIX;
        assert_eq!(ll, rl, "anchor pao na limbu {}", k);
        col[BBc][k]=BaseElement::new(bb[k]); col[Dc][k]=BaseElement::new(d[k]);
        col[LCIN][k]=BaseElement::new(lcin); col[L_COL][k]=BaseElement::new(ll);
        col[RCIN][k]=BaseElement::new(rcin); col[R_COL][k]=BaseElement::new(rl);
        let lb=bits(ll,CBW); let lcb=bits(lc,LCW); let rb=bits(rl,CBW); let rcb=bits(rc,RCW);
        for t in 0..CBW { col[LBITS+t][k]=lb[t]; col[RBITS+t][k]=rb[t]; }
        for t in 0..LCW { col[LCBITS+t][k]=lcb[t]; } for t in 0..RCW { col[RCBITS+t][k]=rcb[t]; }
        mcin = cnext; lcin = lc; rcin = rc;
    }
    (col, ac)
}
fn build_trace(col: &[Vec<BaseElement>]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    t.fill(|s| { for j in 0..WIDTH { s[j]=col[j][0]; } },
           |step,s| { for j in 0..WIDTH { s[j]=col[j][step+1]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = FuseAir; type Trace = TraceTable<BaseElement>;
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
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/fuse.txt")).expect("fuse.txt");
    let mut it = txt.lines();
    let p = |s: &str| -> Vec<u64> { s.trim().split(',').map(|x| x.parse().unwrap()).collect() };
    let a=p(it.next().unwrap()); let c=p(it.next().unwrap()); let bb=p(it.next().unwrap()); let d=p(it.next().unwrap());
    let (col, ac) = build(&a, &c, &bb, &d);
    println!("== MILESTONE D1: FUZIJA mnozilac(a·c) + anchor u jednom tragu ==");
    println!("bez faznog selektora: AC = izlaz mnozioca = ulaz anchora (unutar-red)");
    println!("trag: {} redova x {} kolona (169 mnozilac + 43 anchor, deljen AC) < 255", N, WIDTH);

    let pi = Pub { a: tb(&a), c: tb(&c), bb: tb(&bb), d: tb(&d), ac: tb(&ac) };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&col);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64()*1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<FuseAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64()*1000.0;
    println!("dokaz {:.1} KB ; prove {:.0} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64/1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    // negativan: pokvari a -> AC pogresno -> anchor pada (dokazuje da fuzija drzi)
    let mut abad = pi.a.clone(); abad[10] = abad[10] + BaseElement::ONE;
    let r1 = winterfell::verify::<FuseAir, H, RC>(proof.clone(), Pub { a: abad, ..pi.clone() }, &mo);
    println!("lazno a (lomi AC->anchor): {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let mut dbad = d.clone(); dbad[50] ^= 1;
    let r2 = winterfell::verify::<FuseAir, H, RC>(proof.clone(), Pub { d: tb(&dbad), ..pi.clone() }, &mo);
    println!("lazno |D|: {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: mnozilac+anchor fuzionisani u jedan trag ({} kolona, bez selektora).", WIDTH);
}
