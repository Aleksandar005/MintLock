// INTEGRISANI AIR: rho lanac + LogUp range-check u JEDNOM dokazu.
// - Glavni trag: rho lanac (a'=c, b'=-b+2kc, c'=a-kb+k²c, W1=c-b', W2=c+b'-1),
//   svaki red = jedna rho runda. Lanac ciklise (period 2) pa je SVAKI red validna
//   rho tranzicija -> nema selektora/gejta.
// - Aux trag: DVA LogUp akumulatora koji range-check-uju BM=|b| i W1 protiv
//   DELJENE tablice T=[0,2^15). Zamenjuje bit-dekompoziciju iz mulseg4.
// Kolone: 11 glavnih + 2 aux (vs mulseg4: 164). Tablica 32768 redova (jeftino, log FRI).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const N: usize = 1 << 15;    // 32768 = velicina tablice [0,2^15) i duzina traga
// glavne kolone
const A: usize = 0;
const C: usize = 1;
const BM: usize = 2;   // |b|
const SB: usize = 3;   // sign b
const KM: usize = 4;   // |k|
const SK: usize = 5;   // sign k
const W1: usize = 6;
const W2: usize = 7;
const T: usize = 8;    // tablica [0,N)
const MBM: usize = 9;  // visestrukost za BM LogUp
const MW1: usize = 10; // visestrukost za W1 LogUp
const MAIN_W: usize = 11;

fn signed<E: FieldElement>(mag: E, sign: E) -> E { (E::ONE - sign - sign) * mag }

// ---------- custom Trace sa aux (2 LogUp akumulatora) ----------
struct IntTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl IntTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        IntTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [2], [1]), length }
    }
}
impl Trace for IntTrace {
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
        &mut self, aux_segments: &[ColMatrix<E>], rand: &[E],
    ) -> Option<ColMatrix<E>> {
        if !aux_segments.is_empty() { return None; }
        let alpha = rand[0];
        let n = self.length;
        // term za kolonu `col` sa multiplicitetom `mcol`
        let mk = |col: usize, mcol: usize| -> Vec<E> {
            let mut s = vec![E::ZERO; n];
            let term = |i: usize| -> E {
                let w = E::from(self.main.get(col, i));
                let t = E::from(self.main.get(T, i));
                let m = E::from(self.main.get(mcol, i));
                (alpha - w).inv() - m * (alpha - t).inv()
            };
            s[0] = term(0);
            for i in 1..n { s[i] = s[i - 1] + term(i); }
            s
        };
        Some(ColMatrix::new(vec![mk(BM, MBM), mk(W1, MW1)]))
    }
}

// ---------- Air ----------
#[derive(Clone)]
struct Pub {
    a0: BaseElement, c0: BaseElement, bm0: BaseElement, sb0: BaseElement,
    mbm0: BaseElement, w1_0: BaseElement, mw1_0: BaseElement, n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.a0, self.c0, self.bm0, self.sb0, self.mbm0, self.w1_0, self.mw1_0,
             BaseElement::new(self.n as u64)]
    }
}

struct IntAir { context: AirContext<BaseElement>, p: Pub }
impl Air for IntAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main_deg = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(1), // a'=c
            TransitionConstraintDegree::new(2), // b'=-b+2kc
            TransitionConstraintDegree::new(4), // c'=a-kb+k^2c
            TransitionConstraintDegree::new(2), // W1
            TransitionConstraintDegree::new(2), // W2
            TransitionConstraintDegree::new(2), // SB bool
            TransitionConstraintDegree::new(2), // SK bool
        ];
        let aux_deg = vec![TransitionConstraintDegree::new(3), TransitionConstraintDegree::new(3)];
        let context = AirContext::new_multi_segment(ti, main_deg, aux_deg, 5, 4, options);
        IntAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let two = E::from(BaseElement::new(2));
        let sb = signed(cur[BM], cur[SB]);
        let sk = signed(cur[KM], cur[SK]);
        let sbp = signed(nxt[BM], nxt[SB]);
        let kk = cur[KM] * cur[KM];
        result[0] = nxt[T] - cur[T] - one;                                   // T advance
        result[1] = nxt[A] - cur[C];                                         // a'=c
        result[2] = sbp - (E::ZERO - sb + two * sk * cur[C]);                // b'
        result[3] = nxt[C] - (cur[A] - sk * sb + kk * cur[C]);               // c'
        result[4] = cur[W1] - (cur[C] - sbp);                               // W1=c-b'
        result[5] = cur[W2] - (cur[C] + sbp - one);                         // W2=c+b'-1
        result[6] = cur[SB] * (cur[SB] - one);
        result[7] = cur[SK] * (cur[SK] - one);
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(T, 0, BaseElement::ZERO),
            Assertion::single(A, 0, self.p.a0),
            Assertion::single(C, 0, self.p.c0),
            Assertion::single(BM, 0, self.p.bm0),
            Assertion::single(SB, 0, self.p.sb0),
        ]
    }

    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let alpha = rand.get_segment_elements(0)[0];
        let mn = main.next();
        let t = E::from(mn[T]);
        // BM akumulator (aux kolona 0)
        let wbm = E::from(mn[BM]); let mbm = E::from(mn[MBM]);
        result[0] = (aux.next()[0] - aux.current()[0]) * (alpha - wbm) * (alpha - t)
            - ((alpha - t) - mbm * (alpha - wbm));
        // W1 akumulator (aux kolona 1)
        let ww1 = E::from(mn[W1]); let mw1 = E::from(mn[MW1]);
        result[1] = (aux.next()[1] - aux.current()[1]) * (alpha - ww1) * (alpha - t)
            - ((alpha - t) - mw1 * (alpha - ww1));
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = |w0: BaseElement, m0: BaseElement| -> E {
            (alpha - E::from(w0)).inv() - E::from(m0) * alpha.inv()
        };
        vec![
            Assertion::single(0, 0, term0(self.p.bm0, self.p.mbm0)),
            Assertion::single(0, self.p.n - 1, E::ZERO),
            Assertion::single(1, 0, term0(self.p.w1_0, self.p.mw1_0)),
            Assertion::single(1, self.p.n - 1, E::ZERO),
        ]
    }
}

// ---------- Prover ----------
struct P { options: ProofOptions }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = IntAir;
    type Trace = IntTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        Pub {
            a0: t.main.get(A, 0), c0: t.main.get(C, 0), bm0: t.main.get(BM, 0),
            sb0: t.main.get(SB, 0), mbm0: t.main.get(MBM, 0),
            w1_0: t.main.get(W1, 0), mw1_0: t.main.get(MW1, 0), n: t.length(),
        }
    }
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
fn mag(x: i128) -> BaseElement { BaseElement::new(x.unsigned_abs() as u64) }
fn sgn(x: i128) -> BaseElement { if x < 0 { BaseElement::ONE } else { BaseElement::ZERO } }

fn build(tamper_bm: Option<usize>) -> (IntTrace, Pub) {
    // rho lanac: pocetak (un-normalizovan), k=-1 na rundi 1, dalje k=0 (swap-ciklus)
    let mut a = vec![0i128; N]; let mut b = vec![0i128; N]; let mut c = vec![0i128; N];
    a[0] = 915; b[0] = 2159; c[0] = 3860;
    for i in 0..N - 1 {
        let k: i128 = if i == 1 { -1 } else { 0 };
        a[i + 1] = c[i];
        b[i + 1] = -b[i] + 2 * k * c[i];
        c[i + 1] = a[i] - k * b[i] + k * k * c[i];
    }
    // kolone
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    let mut bm_raw = vec![0i128; N]; let mut w1_raw = vec![0i128; N];
    for i in 0..N {
        let (w1, w2) = if i < N - 1 {
            let bp = b[i + 1];
            (c[i] - bp, c[i] + bp - 1)
        } else {
            (0i128, 0i128) // poslednji red nije vezan rho tranzicijom -> in-range 0
        };
        let mut bmv = b[i].unsigned_abs() as i128;
        if let Some(idx) = tamper_bm { if i == idx { bmv = 40000; } } // van [0,2^15)
        bm_raw[i] = bmv; w1_raw[i] = w1;
        col[A][i] = mag(a[i]); col[C][i] = mag(c[i]);
        col[BM][i] = BaseElement::new(bmv as u64); col[SB][i] = sgn(b[i]);
        col[KM][i] = mag(if i < N - 1 && i == 1 { -1 } else { 0 });
        col[SK][i] = sgn(if i == 1 { -1 } else { 0 });
        col[W1][i] = mag(w1); col[W2][i] = mag(w2);
        col[T][i] = BaseElement::new(i as u64);
    }
    // multipliciteti (broj pojavljivanja vrednosti == i u koloni)
    let mut mbm = vec![0u64; N]; let mut mw1 = vec![0u64; N];
    for i in 0..N {
        let v = bm_raw[i]; if (0..N as i128).contains(&v) { mbm[v as usize] += 1; }
        let v = w1_raw[i]; if (0..N as i128).contains(&v) { mw1[v as usize] += 1; }
    }
    for i in 0..N { col[MBM][i] = BaseElement::new(mbm[i]); col[MW1][i] = BaseElement::new(mw1[i]); }

    let p = Pub {
        a0: col[A][0], c0: col[C][0], bm0: col[BM][0], sb0: col[SB][0],
        mbm0: col[MBM][0], w1_0: col[W1][0], mw1_0: col[MW1][0], n: N,
    };
    (IntTrace::new(col), p)
}

fn run(tamper: Option<usize>, label: &str, expect_ok: bool) {
    let (trace, p) = build(tamper);
    let prover = P { options: ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31) };
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64() * 1000.0;
        let pb = proof.to_bytes().len();
        let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok = winterfell::verify::<IntAir, H, RC>(proof, p.clone(), &mo).is_ok();
        (pb, sec, pm, ok)
    }));
    match res {
        Ok((pb, sec, pm, ok)) => {
            println!("{}: verify={} (ocek {}) ; dokaz {:.1} KB ; prove {:.0} ms ; sec {}",
                label, if ok {"PASS"} else {"FAIL"}, if expect_ok {"PASS"} else {"FAIL"},
                pb as f64/1024.0, pm, sec);
            if ok != expect_ok { std::process::exit(2); }
        }
        Err(_) => {
            println!("{}: PANIC/odbijen (ocek {})", label, if expect_ok {"PASS"} else {"FAIL"});
            if expect_ok { std::process::exit(2); }
        }
    }
}

fn main() {
    println!("== INTEGRISANO: rho lanac + LogUp (BM,W1) ; {} kolona glavni + 2 aux ; tablica [0,2^15) ==", MAIN_W);
    run(None, "[validan]  rho lanac + range-check", true);
    run(Some(3), "[negativan] BM[3] van opsega (40000)", false);
    println!("\nSVE PROSLO: rho + LogUp integrisano u jedan dokaz.");
}
