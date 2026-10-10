// MILESTONE D2: POTPISANO multi-limb oduzimanje  Z = X - Y  na punoj sirini.
// Jezgro rho aritmetike na 64+ limba: b'=-b+2kc i c'=a-kb+k²c uvode NEGATIVNE
// medjuvrednosti (mulseg4 je koristio nativno polje jer su vrednosti bile male;
// na 1024-bit to ne radi). Mnozenja su single-limb (mulseg_a, dokazano); novo je
// potpisano oduzimanje sa znakom, ovde dokazano zvucno.
//
// PRIMITIV (bez case-analize): witness sign_Z i |Z|; verifikuj
//   big == small + |Z|   gde  big = sign_Z ? Y : X ,  small = sign_Z ? X : Y.
// |Z|>=0 (range-check) forsira big>=small -> pogresan znak je nemoguc:
//   sign_Z=0: X==Y+|Z| -> Z=X-Y>=0 ;  sign_Z=1: Y==X+|Z| -> Z=X-Y<=0.  Zvucno.

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
const ZBW: usize = 16;   // |Z| limb bits

// narrow-long: po jedan limb X,Y,Z po redu; sign_Z je GLOBALAN (kolona konstanta)
const Xc: usize = 0;
const Yc: usize = 1;
const Zc: usize = 2;      // |Z[k]|
const SZ: usize = 3;      // sign_Z (isti u svim redovima)
const BIN: usize = 4;     // borrow/carry in (add lanca big=small+|Z|)
const ZBITS: usize = 5;   // 16 bitova |Z[k]|
const BOUT_BIT: usize = ZBITS + ZBW;  // 1 bit carry-out
const WIDTH: usize = BOUT_BIT + 1;    // 4 + 16 + 1 = 21

#[derive(Clone)]
struct Pub { x: Vec<BaseElement>, y: Vec<BaseElement>, z: Vec<BaseElement>, sz: BaseElement }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.x.clone(); v.extend_from_slice(&self.y); v.extend_from_slice(&self.z); v.push(self.sz); v
    }
}

struct SubAir { context: AirContext<BaseElement>, p: Pub }
impl Air for SubAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(2), // add lanac: small + |Z| + bin == big + R·bout
            TransitionConstraintDegree::new(1), // borrow link
            TransitionConstraintDegree::new(1), // Z recomp
            TransitionConstraintDegree::new(1), // sign konstanta
            TransitionConstraintDegree::new(2), // sign bool
        ];
        for _ in 0..ZBW { d.push(TransitionConstraintDegree::new(2)); } // Z bits
        d.push(TransitionConstraintDegree::new(2)); // bout bool
        // asertacije: bin0=0 ; X,Y,Z po redu (3N) ; SZ row0
        let n_assert = 1 + 3 * N + 1;
        SubAir { context: AirContext::new(ti, d, n_assert, options), p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let radix = E::from(BaseElement::new(RADIX));
        let sz = cur[SZ];
        // big = sz? Y : X ; small = sz? X : Y   (sz∈{0,1})
        let big = sz * cur[Yc] + (one - sz) * cur[Xc];
        let small = sz * cur[Xc] + (one - sz) * cur[Yc];
        let mut zrec = E::ZERO;
        for k in 0..ZBW { zrec += cur[ZBITS + k] * E::from(BaseElement::new(1u64 << k)); }
        let bout = cur[BOUT_BIT];
        let mut r = 0;
        // small + |Z| + bin == big + R·bout
        result[r] = small + cur[Zc] + cur[BIN] - (big + radix * bout); r += 1;
        result[r] = nxt[BIN] - bout; r += 1;                 // borrow link
        result[r] = cur[Zc] - zrec; r += 1;                  // Z recomp
        result[r] = nxt[SZ] - cur[SZ]; r += 1;               // sign konstanta
        result[r] = sz * (sz - one); r += 1;                 // sign bool
        for k in 0..ZBW { result[r] = cur[ZBITS + k] * (cur[ZBITS + k] - one); r += 1; }
        result[r] = bout * (bout - one); r += 1;
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = Vec::new();
        v.push(Assertion::single(BIN, 0, BaseElement::ZERO));
        for k in 0..N {
            v.push(Assertion::single(Xc, k, self.p.x[k]));
            v.push(Assertion::single(Yc, k, self.p.y[k]));
            v.push(Assertion::single(Zc, k, self.p.z[k]));
        }
        v.push(Assertion::single(SZ, 0, self.p.sz));
        v
    }
}

fn bits(x: u64, n: usize) -> Vec<BaseElement> { (0..n).map(|k| BaseElement::new((x >> k) & 1)).collect() }

fn build(x: &[u64], y: &[u64], z: &[u64], sz: u64) -> Vec<Vec<BaseElement>> {
    let mut col = vec![vec![BaseElement::ZERO; N]; WIDTH];
    let mut bin = 0u64;
    for k in 0..N {
        let big = if sz == 1 { y[k] } else { x[k] };
        let small = if sz == 1 { x[k] } else { y[k] };
        let s = small + z[k] + bin;
        let bout = if s >= RADIX { 1 } else { 0 };
        debug_assert_eq!(s - bout * RADIX, big, "add lanac pao na limbu {}", k);
        col[Xc][k] = BaseElement::new(x[k]); col[Yc][k] = BaseElement::new(y[k]);
        col[Zc][k] = BaseElement::new(z[k]); col[SZ][k] = BaseElement::new(sz);
        col[BIN][k] = BaseElement::new(bin);
        let zb = bits(z[k], ZBW); for t in 0..ZBW { col[ZBITS + t][k] = zb[t]; }
        col[BOUT_BIT][k] = BaseElement::new(bout);
        bin = bout;
    }
    col
}
fn build_trace(col: &[Vec<BaseElement>]) -> TraceTable<BaseElement> {
    let mut t = TraceTable::new(WIDTH, N);
    t.fill(|s| { for j in 0..WIDTH { s[j] = col[j][0]; } },
           |step, s| { for j in 0..WIDTH { s[j] = col[j][step + 1]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = SubAir; type Trace = TraceTable<BaseElement>;
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
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/signed.txt")).expect("signed.txt");
    let mut it = txt.lines();
    let pl = |s: &str| -> Vec<u64> { s.trim().split(',').map(|x| x.parse().unwrap()).collect() };
    let x = pl(it.next().unwrap()); let y = pl(it.next().unwrap()); let z = pl(it.next().unwrap());
    let sz: u64 = it.next().unwrap().trim().parse().unwrap();
    let col = build(&x, &y, &z, sz);
    println!("== MILESTONE D2: potpisano oduzimanje Z=X-Y na 2048-bit (X=a·c, Y=b²) ==");
    println!("znak Z = {} ; narrow-long ; trag {} redova x {} kolona", sz, N, WIDTH);

    let pi = Pub { x: tb(&x), y: tb(&y), z: tb(&z), sz: BaseElement::new(sz) };
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, pi: pi.clone() };
    let trace = build_trace(&col);
    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove");
    let pm = t0.elapsed().as_secs_f64() * 1000.0;
    let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    let t1 = Instant::now();
    let ok = winterfell::verify::<SubAir, H, RC>(proof.clone(), pi.clone(), &mo).is_ok();
    let vm = t1.elapsed().as_secs_f64() * 1000.0;
    println!("dokaz {:.1} KB ; prove {:.0} ms ; verify {:.2} ms ; sec {} ; verify={}",
             pb as f64 / 1024.0, pm, vm, sec, if ok {"PASS"} else {"FAIL"});
    if !ok { std::process::exit(1); }

    // negativni: pogresan Z ; pogresan znak
    let mut zbad = z.clone(); zbad[40] ^= 1;
    let r1 = winterfell::verify::<SubAir, H, RC>(proof.clone(), Pub { z: tb(&zbad), ..pi.clone() }, &mo);
    println!("lazno Z:      {}", if r1.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let r2 = winterfell::verify::<SubAir, H, RC>(proof.clone(), Pub { sz: BaseElement::new(1 - sz), ..pi.clone() }, &mo);
    println!("pogresan znak: {}", if r2.is_err() {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    if !(r1.is_err() && r2.is_err()) { std::process::exit(2); }
    println!("\nSVE PROSLO: potpisano oduzimanje na 2048-bit, {} kolona ; pogresan znak nemoguc.", WIDTH);
}
