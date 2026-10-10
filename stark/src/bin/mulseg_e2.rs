// MILESTONE E2: ulancavanje dva rho segmenta + D-vezivanje (protokol, mala forma).
// Segment = rho lanac (7 rundi) + DISC-INVARIJANTA 4ac-b²==|D| po redu (D-vezivanje).
// Pomocne kolone (SBV=potpisano b, SKV=potpisano k, KK=k²) drze max degree na 2.

use std::fs;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix, Air, AirContext, Assertion, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain, StarkProof,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const N: usize = 8;
const A: usize = 0; const C: usize = 1; const BM: usize = 2; const SB: usize = 3;
const KM: usize = 4; const SK: usize = 5; const SBV: usize = 6; const SKV: usize = 7; const KK: usize = 8;
const CTR: usize = 9;
const WIDTH: usize = 10;

fn signed<E: FieldElement>(mag: E, sign: E) -> E { (E::ONE - sign - sign) * mag }

#[derive(Clone, PartialEq, Debug)]
struct Form { a: BaseElement, bm: BaseElement, sb: BaseElement, c: BaseElement }
#[derive(Clone)]
struct Pub { fin: Form, fout: Form, dabs: BaseElement }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.fin.a, self.fin.bm, self.fin.sb, self.fin.c,
             self.fout.a, self.fout.bm, self.fout.sb, self.fout.c, self.dabs]
    }
}

struct SegAir { context: AirContext<BaseElement>, p: Pub }
impl Air for SegAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let d = vec![
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(1), // CTR advance (pun stepen)
        ];
        SegAir { context: AirContext::new(ti, d, 9, options), p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let two = E::from(BaseElement::new(2)); let four = E::from(BaseElement::new(4));
        let dabs = E::from(self.p.dabs);
        result[0] = nxt[A] - cur[C];
        result[1] = nxt[SBV] - (E::ZERO - cur[SBV] + two*cur[SKV]*cur[C]);
        result[2] = nxt[C] - (cur[A] - cur[SKV]*cur[SBV] + cur[KK]*cur[C]);
        result[3] = four*cur[A]*cur[C] - cur[BM]*cur[BM] - dabs;
        result[4] = cur[SBV] - signed(cur[BM], cur[SB]);
        result[5] = cur[SKV] - signed(cur[KM], cur[SK]);
        result[6] = cur[KK] - cur[KM]*cur[KM];
        result[7] = cur[SB]*(cur[SB]-one);
        result[8] = cur[SK]*(cur[SK]-one);
        result[9] = nxt[CTR] - cur[CTR] - one;   // CTR = 0,1,2,... (pun stepen trag-polinoma)
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = N - 1;
        vec![
            Assertion::single(A, 0, self.p.fin.a), Assertion::single(BM, 0, self.p.fin.bm),
            Assertion::single(SB, 0, self.p.fin.sb), Assertion::single(C, 0, self.p.fin.c),
            Assertion::single(A, last, self.p.fout.a), Assertion::single(BM, last, self.p.fout.bm),
            Assertion::single(SB, last, self.p.fout.sb), Assertion::single(C, last, self.p.fout.c),
            Assertion::single(CTR, 0, BaseElement::ZERO),
        ]
    }
}

fn mag(x: i128) -> BaseElement { BaseElement::new(x.unsigned_abs() as u64) }
fn sgn(x: i128) -> BaseElement { if x < 0 { BaseElement::ONE } else { BaseElement::ZERO } }
fn fe(x: i128) -> BaseElement { if x >= 0 { BaseElement::new(x as u64) } else { BaseElement::ZERO - BaseElement::new((-x) as u64) } }

fn build_trace(a: &[i128], b: &[i128], c: &[i128], k: &[i128]) -> TraceTable<BaseElement> {
    let mut rows = vec![[BaseElement::ZERO; WIDTH]; N];
    for i in 0..N {
        let ki = if i < N-1 { k[i] } else { 0 };
        rows[i][A]=mag(a[i]); rows[i][C]=mag(c[i]); rows[i][BM]=mag(b[i]); rows[i][SB]=sgn(b[i]);
        rows[i][KM]=mag(ki); rows[i][SK]=sgn(ki);
        rows[i][SBV]=fe(b[i]); rows[i][SKV]=fe(ki); rows[i][KK]=BaseElement::new((ki*ki) as u64);
        rows[i][CTR]=BaseElement::new(i as u64);
    }
    let mut t = TraceTable::new(WIDTH, N); let r0=rows[0]; let owned=rows.clone();
    t.fill(|s| { for j in 0..WIDTH { s[j]=r0[j]; } }, |step,s| { let nr=owned[step+1]; for j in 0..WIDTH { s[j]=nr[j]; } });
    t
}

struct P { options: ProofOptions, pi: Pub }
impl Prover for P {
    type BaseField = BaseElement; type Air = SegAir; type Trace = TraceTable<BaseElement>;
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

fn form_at(a:&[i128],b:&[i128],c:&[i128],i:usize) -> Form { Form { a: mag(a[i]), bm: mag(b[i]), sb: sgn(b[i]), c: mag(c[i]) } }

fn prove_seg(a:&[i128],b:&[i128],c:&[i128],k:&[i128], lo:usize, dabs:BaseElement) -> (StarkProof, Pub) {
    let sa=&a[lo..lo+N]; let sb=&b[lo..lo+N]; let sc=&c[lo..lo+N]; let sk=&k[lo..lo+N-1];
    let pi = Pub { fin: form_at(a,b,c,lo), fout: form_at(a,b,c,lo+N-1), dabs };
    let prover = P { options: ProofOptions::new(36,8,16,FieldExtension::Quadratic,4,31), pi: pi.clone() };
    let proof = prover.prove(build_trace(sa,sb,sc,sk)).expect("prove");
    (proof, pi)
}
fn verify_seg(proof: StarkProof, pi: Pub) -> bool {
    let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
    winterfell::verify::<SegAir,H,RC>(proof, pi, &mo).is_ok()
}

fn main() {
    let txt = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/data/e2.txt")).expect("e2.txt");
    let mut it = txt.lines();
    let dabs_u: u64 = it.next().unwrap().trim().parse().unwrap();
    let dabs = BaseElement::new(dabs_u);
    let mut a=vec![]; let mut b=vec![]; let mut c=vec![];
    for _ in 0..15 {
        let row: Vec<i128> = it.next().unwrap().trim().split(',').map(|x| x.parse().unwrap()).collect();
        a.push(row[0]); b.push(row[1]); c.push(row[2]);
    }
    let k: Vec<i128> = it.next().unwrap().trim().split(',').map(|x| x.parse().unwrap()).collect();

    println!("== MILESTONE E2: ulancavanje dva rho segmenta + D-vezivanje ==");
    println!("|D| = {} ; segment = 7 rundi + disc-invarijanta 4ac-b²==|D| po redu", dabs_u);

    let (p1, pi1) = prove_seg(&a,&b,&c,&k, 0, dabs);
    let (p2, pi2) = prove_seg(&a,&b,&c,&k, 7, dabs);
    let v1 = verify_seg(p1.clone(), pi1.clone());
    let v2 = verify_seg(p2.clone(), pi2.clone());
    println!("\nseg1 (F0->F7):  verify={} ; dokaz {:.1} KB", if v1 {"PASS"} else {"FAIL"}, p1.to_bytes().len() as f64/1024.0);
    println!("seg2 (F7->F14): verify={} ; dokaz {:.1} KB", if v2 {"PASS"} else {"FAIL"}, p2.to_bytes().len() as f64/1024.0);
    assert!(v1 && v2);

    let chain_ok = pi1.fout == pi2.fin;
    let dbind_ok = pi1.dabs == pi2.dabs;
    println!("\n== ULANCAVANJE (boundary I/O) ==");
    println!("seg1.F_out == seg2.F_in : {}", if chain_ok {"PASS"} else {"FAIL"});
    println!("seg1.|D| == seg2.|D|    : {}  (D-vezivanje)", if dbind_ok {"PASS"} else {"FAIL"});
    assert!(chain_ok && dbind_ok);

    println!("\n== NEGATIVNI TESTOVI ==");
    let mut pi2_bad = pi2.clone(); pi2_bad.fin.a = pi2_bad.fin.a + BaseElement::ONE;
    let n1 = pi1.fout != pi2_bad.fin;
    println!("prekinut lanac (F_in != F_out): {}", if n1 {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let vD = verify_seg(p2.clone(), Pub { dabs: BaseElement::new(dabs_u + 1), ..pi2.clone() });
    println!("D-vezivanje (lazan |D|):        {}", if !vD {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});
    let vF = verify_seg(p1.clone(), Pub { fout: Form { a: pi1.fout.a + BaseElement::ONE, ..pi1.fout.clone() }, ..pi1.clone() });
    println!("lazan F_out (seg1):             {}", if !vF {"ODBIJEN [ok]"} else {"PRIHVACEN [GRESKA!]"});

    if !(n1 && !vD && !vF) { println!("\nNEGATIVAN TEST PAO!"); std::process::exit(2); }
    println!("\nSVE PROSLO: dve runde ulancane preko boundary I/O, D vezano, falsifikati padaju.");
}
