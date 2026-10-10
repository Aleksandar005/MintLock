// LogUp RANGE-CHECK preko pomocnog (auxiliary) trace segmenta.
// Dokazuje da SVE vrednosti u koloni W leze u [0, N) (tablica), koristeci
// logaritamsko-izvod identitet sa izazovom alpha (Fiat-Shamir, posle commit-a
// glavnog traga):
//     Σ_i 1/(alpha - W_i)  ==  Σ_j M_j/(alpha - T_j)
// gde je T_j = j (tablica [0,N)) i M_j = visestrukost vrednosti j medju W.
// Identitet vazi (nad slucajnim alpha) akko je {W_i} ⊆ {T_j} = [0,N).
//
// POENTA (motiv iz mulseg4): range-check MNOGO vrednosti u ~4 kolone
// (W, T, M, + 1 aux) umesto ~30 boolean kolona PO vrednosti. Jedna tablica
// se deli izmedju svih range-check-ova u celom reduce-u (amortizacija).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const W_COL: usize = 0;
const T_COL: usize = 1;
const M_COL: usize = 2;
const MAIN_W: usize = 3;

// ---------- custom Trace sa aux segmentom ----------
struct LogUpTrace {
    main: ColMatrix<BaseElement>,
    layout: TraceLayout,
    length: usize,
}
impl LogUpTrace {
    fn new(w: Vec<BaseElement>, t: Vec<BaseElement>, m: Vec<BaseElement>) -> Self {
        let length = w.len();
        let main = ColMatrix::new(vec![w, t, m]);
        // main_width=3, jedan aux segment sirine 1, sa 1 slucajnim elementom (alpha)
        let layout = TraceLayout::new(MAIN_W, [1], [1]);
        LogUpTrace { main, layout, length }
    }
}
impl Trace for LogUpTrace {
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
        &mut self, aux_segments: &[ColMatrix<E>], rand_elements: &[E],
    ) -> Option<ColMatrix<E>> {
        if !aux_segments.is_empty() { return None; }
        let alpha = rand_elements[0];
        let n = self.length;
        let term = |i: usize| -> E {
            let w = E::from(self.main.get(W_COL, i));
            let t = E::from(self.main.get(T_COL, i));
            let m = E::from(self.main.get(M_COL, i));
            (alpha - w).inv() - m * (alpha - t).inv()
        };
        let mut s = vec![E::ZERO; n];
        s[0] = term(0);
        for i in 1..n { s[i] = s[i - 1] + term(i); }
        Some(ColMatrix::new(vec![s]))
    }
}

// ---------- Air ----------
#[derive(Clone)]
struct PubInputs { w0: BaseElement, m0: BaseElement, n: usize }
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.w0, self.m0, BaseElement::new(self.n as u64)]
    }
}

struct LogUpAir { context: AirContext<BaseElement>, w0: BaseElement, m0: BaseElement, n: usize }

impl Air for LogUpAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(ti: TraceInfo, pi: PubInputs, options: ProofOptions) -> Self {
        let main_deg = vec![TransitionConstraintDegree::new(1)]; // T advance
        let aux_deg = vec![TransitionConstraintDegree::new(3)];  // LogUp
        let context = AirContext::new_multi_segment(ti, main_deg, aux_deg, 3, 2, options);
        LogUpAir { context, w0: pi.w0, m0: pi.m0, n: pi.n }
    }

    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    // glavni: tablica T raste za 1 svaki red -> T = [0, N)
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        result[0] = nxt[T_COL] - cur[T_COL] - E::ONE;
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(T_COL, 0, BaseElement::ZERO),     // tablica pocinje od 0
            Assertion::single(W_COL, 0, self.w0),               // veze row0 za javne ulaze
            Assertion::single(M_COL, 0, self.m0),
        ]
    }

    // aux: (s' - s)(alpha - W')(alpha - T') == (alpha - T') - M'(alpha - W')
    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let alpha = rand.get_segment_elements(0)[0];
        let mn = main.next();
        let w = E::from(mn[W_COL]);
        let t = E::from(mn[T_COL]);
        let m = E::from(mn[M_COL]);
        let s = aux.current()[0];
        let sp = aux.next()[0];
        result[0] = (sp - s) * (alpha - w) * (alpha - t) - ((alpha - t) - m * (alpha - w));
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let w0 = E::from(self.w0);
        let m0 = E::from(self.m0);
        // term_0 = 1/(alpha - W0) - M0/(alpha - 0)
        let term0 = (alpha - w0).inv() - m0 * alpha.inv();
        vec![
            Assertion::single(0, 0, term0),          // s_0 = term_0
            Assertion::single(0, self.n - 1, E::ZERO), // s_{N-1} = ukupna suma = 0
        ]
    }
}

// ---------- Prover ----------
struct P { options: ProofOptions }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = LogUpAir;
    type Trace = LogUpTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> PubInputs {
        PubInputs { w0: t.main.get(W_COL, 0), m0: t.main.get(M_COL, 0), n: t.length() }
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

fn build_columns(witnesses: &[u64], n: usize) -> (Vec<BaseElement>, Vec<BaseElement>, Vec<BaseElement>, Vec<u64>) {
    // W: witnesses (padded do n vrednoscu 0), T: [0,n), M: visestrukost
    let mut w = vec![0u64; n];
    for (i, &x) in witnesses.iter().enumerate() { w[i] = x; }
    // pad ostatak vrednoscu 0 (0 je u tablici) -> uvecava M[0]
    let mut mult = vec![0u64; n];
    for &x in &w { if (x as usize) < n { mult[x as usize] += 1; } else { /* van opsega: nece se izbrojati */ } }
    let wf: Vec<BaseElement> = w.iter().map(|&x| BaseElement::new(x)).collect();
    let tf: Vec<BaseElement> = (0..n as u64).map(BaseElement::new).collect();
    let mf: Vec<BaseElement> = mult.iter().map(|&x| BaseElement::new(x)).collect();
    (wf, tf, mf, w)
}

fn prove_and_verify(witnesses: &[u64], n: usize, label: &str, expect_ok: bool) {
    let (w, t, m, _wraw) = build_columns(witnesses, n);
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options };
    let trace = LogUpTrace::new(w.clone(), t, m.clone());
    let pi = PubInputs { w0: w[0], m0: m[0], n };

    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prover.prove(trace).expect("prove failed");
        let pb_len = proof.to_bytes().len();
        let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok = winterfell::verify::<LogUpAir, H, RC>(proof, pi.clone(), &mo).is_ok();
        (pb_len, sec, ok)
    }));
    match res {
        Ok((pb_len, sec, ok)) => {
            println!("{}: verify={} (ocekivano {}) ; dokaz {} B ({:.1} KB) ; sec {}",
                     label, if ok {"PASS"} else {"FAIL"}, if expect_ok {"PASS"} else {"FAIL"},
                     pb_len, pb_len as f64/1024.0, sec);
            if ok != expect_ok { println!("   >>> NEOCEKIVANO!"); std::process::exit(2); }
        }
        Err(_) => {
            println!("{}: prove/verify PANIC (odbijen)  (ocekivano {})", label, if expect_ok {"PASS"} else {"FAIL"});
            if expect_ok { std::process::exit(2); }
        }
    }
}

fn main() {
    let n = 256usize; // tablica [0,256) = 8-bit range-check
    println!("== LogUp range-check ; tablica [0,{}) ; glavni trag 3 kolone + 1 aux ==", n);
    println!("(range-check {} vrednosti u ~4 kolone umesto ~8 boolean/vrednost)", n);

    // VALIDAN: 256 vrednosti, sve u [0,256), sa ponavljanjima (M varira)
    let good: Vec<u64> = (0..n as u64).map(|i| (i * 173 + 89) % 251).collect();
    println!();
    prove_and_verify(&good, n, "[validan]        sve u opsegu", true);

    // NEGATIVAN 1: jedna vrednost van opsega (300 >= 256) -> identitet ne balansira
    let mut bad = good.clone(); bad[5] = 300;
    prove_and_verify(&bad, n, "[negativan] W[5]=300 (van opsega)", false);

    // NEGATIVAN 2: druga vrednost van opsega (256 tacno na granici)
    let mut bad2 = good.clone(); bad2[100] = 256;
    prove_and_verify(&bad2, n, "[negativan] W[100]=256 (na granici)", false);

    println!("\nSVE PROSLO: LogUp range-check radi; van-opsega vrednosti ODBIJENE.");
}
