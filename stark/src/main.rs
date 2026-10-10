// STARK dokaz Wesolowski verifikacione jednacine (prime-field analog).
//
// On-chain provera koju ugovor radi je: shamir(pi, l, u, r) == reduce(w),
// tj. jointni MSB-first square-and-multiply koji racuna  pi^l * u^r  u grupi.
// Ovde dokazujemo TACNO tu jednacinu u polju Goldilocks (p = 2^64 - 2^32 + 1)
// kao posten razmerni model klasno-grupne dvostruke eksponencijacije:
// prover odradi eksponencijaciju off-chain i napravi TRANSPARENTAN STARK
// (FRI, BEZ trusted setupa); "ugovor" samo proverava dokaz.

use std::time::Instant;

use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, FieldElement, StarkField, ToElements},
    Air, AirContext, Assertion, matrix::ColMatrix, DefaultConstraintEvaluator, DefaultTraceLde,
    EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain, StarkProof, Trace,
    TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const NCOLS: usize = 5;

// -------------------- Javni ulazi --------------------
#[derive(Clone)]
struct PubInputs {
    pi: BaseElement,
    u: BaseElement,
    w: BaseElement,
    l: BaseElement,
    r: BaseElement,
}
impl ToElements<BaseElement> for PubInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.pi, self.u, self.w, self.l, self.r]
    }
}

// -------------------- AIR --------------------
struct DExpAir {
    context: AirContext<BaseElement>,
    pi: BaseElement,
    u: BaseElement,
    w: BaseElement,
    l: BaseElement,
    r: BaseElement,
}

impl Air for DExpAir {
    type BaseField = BaseElement;
    type PublicInputs = PubInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PubInputs, options: ProofOptions) -> Self {
        let degrees = vec![
            TransitionConstraintDegree::new(4), // acc = acc^2 * lb-term * rb-term
            TransitionConstraintDegree::new(2), // lb boolean
            TransitionConstraintDegree::new(2), // rb boolean
            TransitionConstraintDegree::new(1), // lacc rekurencija
            TransitionConstraintDegree::new(1), // racc rekurencija
        ];
        let context = AirContext::new(trace_info, degrees, 6, options);
        DExpAir {
            context,
            pi: pub_inputs.pi,
            u: pub_inputs.u,
            w: pub_inputs.w,
            l: pub_inputs.l,
            r: pub_inputs.r,
        }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic: &[E],
        result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let (acc, lb, rb, lacc, racc) = (cur[0], cur[1], cur[2], cur[3], cur[4]);
        let (acc_n, lacc_n, racc_n) = (nxt[0], nxt[3], nxt[4]);

        let pi = E::from(self.pi);
        let u = E::from(self.u);
        let one = E::ONE;
        let two = E::from(2u32);

        // acc' = acc^2 * (1 + lb*(pi-1)) * (1 + rb*(u-1))
        let mul = (one + lb * (pi - one)) * (one + rb * (u - one));
        result[0] = acc_n - acc * acc * mul;
        result[1] = lb * (lb - one);
        result[2] = rb * (rb - one);
        result[3] = lacc_n - (two * lacc + lb);
        result[4] = racc_n - (two * racc + rb);
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, BaseElement::ONE),
            Assertion::single(3, 0, BaseElement::ZERO),
            Assertion::single(4, 0, BaseElement::ZERO),
            Assertion::single(0, last, self.w),
            Assertion::single(3, last, self.l),
            Assertion::single(4, last, self.r),
        ]
    }
}

// -------------------- Trace builder --------------------
fn build_trace(n: usize, pi: BaseElement, u: BaseElement, l: u64, r: u64) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(NCOLS, n);
    let bit = |x: u64, pos: usize| -> u64 { if pos >= 64 { 0 } else { (x >> pos) & 1 } };
    trace.fill(
        |state| {
            state[0] = BaseElement::ONE; // acc
            let pos0 = n - 2;
            state[1] = BaseElement::new(bit(l, pos0)); // lb
            state[2] = BaseElement::new(bit(r, pos0)); // rb
            state[3] = BaseElement::ZERO; // lacc
            state[4] = BaseElement::ZERO; // racc
        },
        |step, state| {
            let acc = state[0];
            let lb = state[1];
            let rb = state[2];
            let lacc = state[3];
            let racc = state[4];

            let mul_pi = if lb == BaseElement::ONE { pi } else { BaseElement::ONE };
            let mul_u = if rb == BaseElement::ONE { u } else { BaseElement::ONE };
            let acc_next = acc * acc * mul_pi * mul_u;
            let lacc_next = lacc + lacc + lb;
            let racc_next = racc + racc + rb;

            let next_row = step + 1;
            let (lb_next, rb_next) = if next_row <= n - 2 {
                let pos = n - 2 - next_row;
                (bit(l, pos), bit(r, pos))
            } else {
                (0, 0)
            };

            state[0] = acc_next;
            state[1] = BaseElement::new(lb_next);
            state[2] = BaseElement::new(rb_next);
            state[3] = lacc_next;
            state[4] = racc_next;
        },
    );
    trace
}

// -------------------- Prover --------------------
struct DExpProver {
    options: ProofOptions,
    pi: BaseElement,
    u: BaseElement,
}
impl Prover for DExpProver {
    type BaseField = BaseElement;
    type Air = DExpAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> PubInputs {
        let last = trace.length() - 1;
        PubInputs {
            pi: self.pi,
            u: self.u,
            w: trace.get(0, last),
            l: trace.get(3, last),
            r: trace.get(4, last),
        }
    }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self, trace_info: &TraceInfo, main_trace: &ColMatrix<BaseElement>, domain: &StarkDomain<BaseElement>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain)
    }
    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self, air: &'a Self::Air, aux: winterfell::AuxTraceRandElements<E>,
        cc: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux, cc)
    }
}

type H = Blake3_256<BaseElement>;
type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;

fn main() {
    let p = BaseElement::MODULUS;
    let pi = BaseElement::new(0x0123_4567_89ab_cdef % p);
    let u = BaseElement::new(0xfedc_ba98_7654_3210 % p);
    let l: u64 = 0x5f2d_9c17_44a1_0003; // neparno, ~63-bit (analog izazova)
    let r: u64 = 0x1a7b_33e0_91cc_d5f1; // analog 2^T mod l

    let n: usize = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(128);
    assert!(n.is_power_of_two() && n >= 8, "n mora biti stepen dvojke >= 8");
    let w = pi.exp(l) * u.exp(r);

    println!("== Wesolowski verifikaciona jednacina (prime-field analog) ==");
    println!("polje: Goldilocks p = 2^64 - 2^32 + 1");
    println!("pi = {}", pi.as_int());
    println!("u  = {}", u.as_int());
    println!("l  = {}  (~{}-bit)", l, 64 - l.leading_zeros());
    println!("r  = {}", r);
    println!("w  = pi^l * u^r = {}", w.as_int());
    println!("trace: {} redova x {} kolone", n, NCOLS);

    let options = ProofOptions::new(42, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = DExpProver { options: options.clone(), pi, u };

    let trace = build_trace(n, pi, u, l, r);
    assert_eq!(trace.get(0, n - 1), w, "trace ne reprodukuje w");
    assert_eq!(trace.get(3, n - 1), BaseElement::new(l), "lacc != l");
    assert_eq!(trace.get(4, n - 1), BaseElement::new(r), "racc != r");
    println!("[ok] trace reprodukuje (w, l, r) na kraju");

    let t0 = Instant::now();
    let proof = prover.prove(trace).expect("prove failed");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let proof_bytes = proof.to_bytes();
    let sec_conj = proof.security_level::<H>(true);
    let sec_prov = proof.security_level::<H>(false);

    println!("\n== DOKAZ ==");
    println!("vreme dokazivanja      : {:.1} ms", prove_ms);
    println!("velicina dokaza        : {} B ({:.2} KB)", proof_bytes.len(), proof_bytes.len() as f64 / 1024.0);
    println!("sigurnost (conjectured): {} bita", sec_conj);
    println!("sigurnost (proven)     : {} bita", sec_prov);

    let pub_inputs = PubInputs { pi, u, w, l: BaseElement::new(l), r: BaseElement::new(r) };
    let min_opts = winterfell::AcceptableOptions::MinConjecturedSecurity(95);

    let t1 = Instant::now();
    let ok = winterfell::verify::<DExpAir, H, RC>(proof.clone(), pub_inputs.clone(), &min_opts);
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!("\n== VERIFIKACIJA ==");
    match &ok {
        Ok(_) => println!("[PASS] validan dokaz PRIHVACEN za {:.2} ms", verify_ms),
        Err(e) => { println!("[FAIL] validan dokaz ODBIJEN: {:?}", e); std::process::exit(1); }
    }

    // negativni testovi
    let bad_pub = PubInputs { w: w + BaseElement::ONE, ..pub_inputs.clone() };
    let bad1 = winterfell::verify::<DExpAir, H, RC>(proof.clone(), bad_pub, &min_opts);
    println!("neg-test (lazno w)      : {}", if bad1.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });

    let mut tampered = proof_bytes.clone();
    let mididx = tampered.len() / 2;
    tampered[mididx] ^= 0x01;
    let bad2 = StarkProof::from_bytes(&tampered)
        .map_err(|_| ())
        .and_then(|pf| winterfell::verify::<DExpAir, H, RC>(pf, pub_inputs.clone(), &min_opts).map_err(|_| ()));
    println!("neg-test (ostecen dokaz): {}", if bad2.is_err() { "ODBIJEN [ok]" } else { "PRIHVACEN [GRESKA!]" });

    if bad1.is_ok() || bad2.is_ok() { std::process::exit(2); }
    println!("SWEEP n={} proof_B={} prove_ms={:.1} verify_ms={:.2} sec_conj={}", n, proof_bytes.len(), prove_ms, verify_ms, sec_conj);
    println!("\nSVE PROSLO.");
}
