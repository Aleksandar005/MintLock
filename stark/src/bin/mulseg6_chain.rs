// PUNO ULANCAVANJE: rho lanac + deljena LogUp tablica u JEDNOM tragu/dokazu.
// - rho aritmetika (mulseg4) gejtovana selektorom RND, lanac formi red->red
// - |k| svake runde range-check-ovan kroz DELJENU LogUp tablicu (mulseg5),
//   umesto bit-dekompozicije -> range-check overhead je ~3 kolone UKUPNO,
//   nezavisno od broja rundi.
// Poenta koju merimo: kolone padaju sa 164 (mulseg4, 156 range-check) na ~12,
// i ostaju konstantne kad broj rundi/tablica raste (raste samo DUZINA traga).
//
// LogUp sa inverse-helper kolonama (drzi sve constraint-e na stepenu <=2):
//   IK = 1/(alpha-|k|) ; IT = 1/(alpha-T) ; akumulator:
//   s' - s = RND'*IK' - M'*IT'  ; s_0 = contrib_0 ; s_{L-1} = 0
// Identitet Σ RND_i/(alpha-|k|_i) = Σ M_j/(alpha-T_j) vazi akko su svi |k| u [0,L).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const NFORM: usize = 8; // 8 formi = 7 rho rundi (redovi 0..7, RND=1 na 0..6)

// main kolone
const A: usize = 0; const C: usize = 1; const BM: usize = 2; const SB: usize = 3;
const KM: usize = 4; const SK: usize = 5; const RND: usize = 6; const T: usize = 7; const M: usize = 8;
const MAIN_W: usize = 9;
// aux kolone
const S: usize = 0; const IK: usize = 1; const IT: usize = 2;
const AUX_W: usize = 3;

fn signed<E: FieldElement>(mag: E, sign: E) -> E { (E::ONE - sign - sign) * mag }

// ---------- Trace ----------
struct ChainTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl ChainTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        ChainTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [AUX_W], [1]), length }
    }
}
impl Trace for ChainTrace {
    type BaseField = BaseElement;
    fn layout(&self) -> &TraceLayout { &self.layout }
    fn length(&self) -> usize { self.length }
    fn meta(&self) -> &[u8] { &[] }
    fn main_segment(&self) -> &ColMatrix<BaseElement> { &self.main }
    fn read_main_frame(&self, row: usize, frame: &mut EvaluationFrame<BaseElement>) {
        let next = (row + 1) % self.length;
        self.main.read_row_into(row, frame.current_mut());
        self.main.read_row_into(next, frame.next_mut());
    }
    fn build_aux_segment<E: FieldElement<BaseField = BaseElement>>(
        &mut self, aux: &[ColMatrix<E>], rand: &[E],
    ) -> Option<ColMatrix<E>> {
        if !aux.is_empty() { return None; }
        let alpha = rand[0];
        let n = self.length;
        let g = |col, i| E::from(self.main.get(col, i));
        let mut ik = vec![E::ZERO; n]; let mut it = vec![E::ZERO; n]; let mut s = vec![E::ZERO; n];
        for i in 0..n {
            ik[i] = (alpha - g(KM, i)).inv();
            it[i] = (alpha - g(T, i)).inv();
        }
        let contrib = |i: usize| -> E { g(RND, i) * ik[i] - g(M, i) * it[i] };
        s[0] = contrib(0);
        for i in 1..n { s[i] = s[i - 1] + contrib(i); }
        Some(ColMatrix::new(vec![s, ik, it]))
    }
}

// ---------- Air ----------
#[derive(Clone)]
struct Pub {
    a0: BaseElement, c0: BaseElement, bm0: BaseElement, sb0: BaseElement,
    aL: BaseElement, cL: BaseElement, bmL: BaseElement, sbL: BaseElement,
    km0: BaseElement, m0: BaseElement, n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.a0,self.c0,self.bm0,self.sb0,self.aL,self.cL,self.bmL,self.sbL,
             self.km0,self.m0,BaseElement::new(self.n as u64)]
    }
}

struct ChainAir { context: AirContext<BaseElement>, p: Pub }
impl Air for ChainAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(2), // RND bool
            TransitionConstraintDegree::new(2), // SB bool
            TransitionConstraintDegree::new(2), // SK bool
            TransitionConstraintDegree::new(2), // rho a'=c (gated)
            TransitionConstraintDegree::new(4), // rho b' (gated: RND*sk*C)
            TransitionConstraintDegree::new(5), // rho c' (gated: RND*signed_k*signed_b)
        ];
        let aux = vec![
            TransitionConstraintDegree::new(2), // IK helper
            TransitionConstraintDegree::new(2), // IT helper
            TransitionConstraintDegree::new(2), // akumulator
        ];
        // main assertions: T0 + (a,c,bm,sb)@0 + (a,c,bm,sb)@(NFORM-1) = 9 ; aux = 2
        let context = AirContext::new_multi_segment(ti, main, aux, 9, 2, options);
        ChainAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _pp: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE; let two = E::from(BaseElement::new(2));
        let g = cur[RND];
        let sb = signed(cur[BM], cur[SB]);
        let sk = signed(cur[KM], cur[SK]);
        let sbp = signed(nxt[BM], nxt[SB]);
        let kk = cur[KM] * cur[KM];
        result[0] = nxt[T] - cur[T] - one;
        result[1] = cur[RND] * (cur[RND] - one);
        result[2] = cur[SB] * (cur[SB] - one);
        result[3] = cur[SK] * (cur[SK] - one);
        result[4] = g * (nxt[A] - cur[C]);
        result[5] = g * (sbp - (E::ZERO - sb + two * sk * cur[C]));
        result[6] = g * (nxt[C] - (cur[A] - sk * sb + kk * cur[C]));
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let l = NFORM - 1;
        vec![
            Assertion::single(T, 0, BaseElement::ZERO),
            Assertion::single(A, 0, self.p.a0), Assertion::single(C, 0, self.p.c0),
            Assertion::single(BM, 0, self.p.bm0), Assertion::single(SB, 0, self.p.sb0),
            Assertion::single(A, l, self.p.aL), Assertion::single(C, l, self.p.cL),
            Assertion::single(BM, l, self.p.bmL), Assertion::single(SB, l, self.p.sbL),
        ]
    }

    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where F: FieldElement<BaseField = BaseElement>,
            E: FieldElement<BaseField = BaseElement> + ExtensionOf<F> {
        let alpha = rand.get_segment_elements(0)[0];
        let mc = main.current(); let mn = main.next();
        let ac = aux.current(); let an = aux.next();
        // helper: IK*(alpha-KM)=1 ; IT*(alpha-T)=1  (na tekucem redu)
        result[0] = ac[IK] * (alpha - E::from(mc[KM])) - E::ONE;
        result[1] = ac[IT] * (alpha - E::from(mc[T])) - E::ONE;
        // akumulator: s' - s = RND'*IK' - M'*IT'
        result[2] = an[S] - ac[S] - (E::from(mn[RND]) * an[IK] - E::from(mn[M]) * an[IT]);
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        // contrib_0 = RND_0*1/(alpha-KM_0) - M_0/(alpha-0) ; RND_0=1
        let c0 = (alpha - E::from(self.p.km0)).inv() - E::from(self.p.m0) * alpha.inv();
        vec![Assertion::single(S, 0, c0), Assertion::single(S, self.p.n - 1, E::ZERO)]
    }
}

// ---------- Prover ----------
struct P { options: ProofOptions, p: Pub }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = ChainAir;
    type Trace = ChainTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> Pub { self.p.clone() }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self, ti: &TraceInfo, mt: &ColMatrix<BaseElement>, dom: &StarkDomain<BaseElement>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) { DefaultTraceLde::new(ti, mt, dom) }
    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self, air: &'a Self::Air, aux: AuxTraceRandElements<E>,
        cc: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> { DefaultConstraintEvaluator::new(air, aux, cc) }
}

type H = Blake3_256<BaseElement>;
type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;
fn fe(x: i128) -> BaseElement { if x>=0 {BaseElement::new(x as u64)} else {BaseElement::ZERO - BaseElement::new((-x) as u64)} }
fn mg(x: i128) -> BaseElement { BaseElement::new(x.unsigned_abs() as u64) }
fn sg(x: i128) -> BaseElement { if x<0 {BaseElement::ONE} else {BaseElement::ZERO} }

fn run(l: usize, label: &str, expect_ok: bool) {
    // PRAVI lanac (mulseg4), k=[-4,-9,-1,0,0,0,0]
    let a = [319749372i128,21164782,271736,67927,238134,67927,238134,67927];
    let b = [-164528537i128,-4789719,-101529,-34325,34325,-34325,34325,-34325];
    let c = [21164782i128,271736,67927,238134,67927,238134,67927,238134];
    let k = [-4i128,-9,-1,0,0,0,0];

    // izgradi kolone duzine l
    let mut col = vec![vec![BaseElement::ZERO; l]; MAIN_W];
    for i in 0..l { col[T][i] = BaseElement::new(i as u64); } // tablica [0,l)
    // forme u redovima 0..NFORM
    for i in 0..NFORM {
        col[A][i]=mg(a[i]); col[C][i]=mg(c[i]); col[BM][i]=mg(b[i]); col[SB][i]=sg(b[i]);
    }
    // k u round redovima 0..NFORM-1 ; RND=1 tamo
    let mut mult = vec![0u64; l];
    for i in 0..NFORM-1 {
        col[KM][i]=mg(k[i]); col[SK][i]=sg(k[i]); col[RND][i]=BaseElement::ONE;
        let kv = k[i].unsigned_abs() as usize;
        if kv < l { mult[kv]+=1; } // van [0,l) -> neizbrojan (negativan test)
    }
    for j in 0..l { col[M][j]=BaseElement::new(mult[j]); }

    let p = Pub {
        a0:mg(a[0]),c0:mg(c[0]),bm0:mg(b[0]),sb0:sg(b[0]),
        aL:mg(a[NFORM-1]),cL:mg(c[NFORM-1]),bmL:mg(b[NFORM-1]),sbL:sg(b[NFORM-1]),
        km0:mg(k[0]), m0:BaseElement::new(mult[0]), n:l,
    };
    let options = ProofOptions::new(36,8,16,FieldExtension::Quadratic,4,31);
    let prover = P { options, p: p.clone() };
    let trace = ChainTrace::new(col);

    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64()*1000.0;
        let pb = proof.to_bytes().len(); let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let vr = winterfell::verify::<ChainAir,H,RC>(proof, p.clone(), &mo);
        let ok = vr.is_ok();
        (pb, sec, ok, pm)
    }));
    match res {
        Ok((pb,sec,ok,pm)) => {
            println!("{}: verify={} (ocek {}) ; kolone={}m+{}aux ; L={} ; dokaz {:.1}KB ; prove {:.1}ms ; sec {}",
                label, if ok{"PASS"}else{"FAIL"}, if expect_ok{"PASS"}else{"FAIL"},
                MAIN_W, AUX_W, l, pb as f64/1024.0, pm, sec);
            if ok!=expect_ok { println!("  >>> NEOCEKIVANO"); std::process::exit(2); }
        }
        Err(_) => { println!("{}: PANIC/odbijen (ocek {})", label, if expect_ok{"PASS"}else{"FAIL"});
            if expect_ok { std::process::exit(2); } }
    }
}

fn main() {
    println!("== PUNO ULANCAVANJE: rho lanac + deljena LogUp tablica u jednom dokazu ==");
    println!("rho stanje {} kolona + LogUp {} aux kolone = {} UKUPNO (mulseg4 imao 164!)", MAIN_W, AUX_W, MAIN_W+AUX_W);
    println!("range-check |k| svake runde kroz JEDNU deljenu tablicu; kolone konstantne u broju rundi.\n");
    // VALIDAN: tablica [0,16) pokriva max |k|=9
    run(16, "[validan]   tablica [0,16), 7 rundi", true);
    // NEGATIVAN: tablica [0,8) -> |k|=9 (runda 1) van opsega -> LogUp odbija
    run(8, "[negativan] tablica [0,8), |k|=9 van opsega", false);
    println!("\nSVE PROSLO: lanac rundi + deljeni LogUp range-check integrisani; kolone 164 -> {}.", MAIN_W+AUX_W);
}
