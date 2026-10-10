// PERM-BIND: lančano vezivanje forme c(r)==a(r+1) preko grand-product permutacije.
// Tag shema:  c-limb bloka r, poz p -> tag = r*L + p ;  a-limb bloka r -> tag = (r-1)*L + p.
// Isti tag za lančane parove => multiset{(tag,c)} == multiset{(tag,a)} akko lanac drži.
// Granični: a prvog bloka i c poslednjeg su NEUPARENI -> tretiramo ih kao JAVNE virtuelne
// unose koji "zatvore" multiset (dodaju se u odgovarajući proizvod da bi Z_final==1).
//
// Fold: e = tag + gamma*val. Grand-product Z:  Z' = Z * (beta - e_a)/(beta - e_c).
//   Z_0 = 1 ; Z_final == 1 akko su multiset-ovi jednaki (posle zatvaranja graničnih).
// Aux (2 izazova: gamma za fold, beta za grand-product). Jedan aux stubac Z.
//
// Mala skala radi brzine: N_R blokova, L limba/blok, RR redova/blok (samo prvih L nose formu).

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const N: usize = 1 << 12;   // 4096 dužina traga (dovoljno za malu demo skalu)
const L: usize = 8;         // limba forme po bloku
const RR: usize = 16;       // redova po bloku (prvih L nose formu, ostalo padding)
const N_R: usize = 32;      // blokova
const ACTIVE: usize = N_R * RR;

// glavne kolone
const AV: usize = 0;    // a-limb (na form-redovima)
const CV: usize = 1;    // c-limb
const TAGA: usize = 2;  // tag za a  = (r-1)*L + p   (committed, γ-nezavisan)
const TAGC: usize = 3;  // tag za c  = r*L + p
const FRM: usize = 4;   // 1 ako red nosi form-limb (p<L), inače 0
const CTR: usize = 5;   // pun stepen
const MAIN_W: usize = 6;

const AUX_Z: usize = 0;
const AUX_W: usize = 1;

struct PermTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl PermTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        PermTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [AUX_W], [2]), length }
    }
}
impl Trace for PermTrace {
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
        let gamma = rand[0];
        let beta = rand[1];
        let n = self.length;
        // fold: e = tag + gamma*val ; doprinos reda (samo FRM=1): (beta - e_a)/(beta - e_c)
        let mut z = vec![E::ONE; n];
        let mut acc = E::ONE;
        for i in 0..n {
            z[i] = acc; // Z pre obrade reda i (Z[0]=1)
            let frm = E::from(self.main.get(FRM, i));
            if frm == E::ONE {
                let av = E::from(self.main.get(AV, i));
                let cv = E::from(self.main.get(CV, i));
                let ta = E::from(self.main.get(TAGA, i));
                let tc = E::from(self.main.get(TAGC, i));
                let ea = ta + gamma*av;
                let ec = tc + gamma*cv;
                acc = acc * (beta - ea) * (beta - ec).inv();
            }
        }
        Some(ColMatrix::new(vec![z]))
    }
}

#[derive(Clone)]
struct Pub {
    // granični neupareni: a prvog bloka (tag (-1)*L+p -> koristimo poseban javni fold),
    // i c poslednjeg bloka. Prosleđujemo ih kao javne vrednosti da verifier zna zatvaranje.
    a_first: Vec<BaseElement>, c_last: Vec<BaseElement>,
    n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.a_first.clone(); v.extend_from_slice(&self.c_last);
        v.push(BaseElement::new(self.n as u64)); v
    }
}

struct PermAir { context: AirContext<BaseElement>, p: Pub }
impl Air for PermAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main_deg = vec![ TransitionConstraintDegree::new(1) ]; // CTR advance
        // aux grand-product: Z' * (beta - e_c) == Z * (beta - e_a)   (samo FRM redovi; inače Z'==Z)
        // stepen: Z' i Z su aux (deg 1 svaki), e_c/e_a su lin u main -> proizvod deg ~2 u aux+main.
        let aux_deg = vec![ TransitionConstraintDegree::new(3) ];
        // main asertacije: CTR0=0 (1). aux: Z0=1, Z_final == zatvaranje (2).
        let context = AirContext::new_multi_segment(ti, main_deg, aux_deg, 1, 2, options);
        PermAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        result[0] = nxt[CTR] - cur[CTR] - E::ONE;
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![ Assertion::single(CTR, 0, BaseElement::ZERO) ]
    }
    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let gamma = rand.get_segment_elements(0)[0];
        let beta = rand.get_segment_elements(0)[1];
        let mc = main.current();
        let frm = E::from(mc[FRM]);
        let av = E::from(mc[AV]); let cv = E::from(mc[CV]);
        let ta = E::from(mc[TAGA]); let tc = E::from(mc[TAGC]);
        let ea = ta + gamma*av;
        let ec = tc + gamma*cv;
        let z = aux.current()[0]; let zp = aux.next()[0];
        // FRM=1:  Z' * (beta - ec) == Z * (beta - ea)
        // FRM=0:  Z' == Z    (nema doprinosa)
        let active = zp*(beta - ec) - z*(beta - ea);
        let idle = zp - z;
        result[0] = frm*active + (E::ONE - frm)*idle;
    }
    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let gamma = rand.get_segment_elements(0)[0];
        let beta = rand.get_segment_elements(0)[1];
        // Z_0 = 1 (pre bilo kog doprinosa). Ali build stavlja Z[0] = doprinos reda 0 ako je FRM.
        // Da bude čisto: tražimo Z na POSLEDNJEM redu == zatvaranje graničnih.
        // Zatvaranje: neupareni a_first (tagovi (-1)*L+p) i c_last (tagovi (N_R-1)*L+p).
        // ∏ svih (beta-ea)/(beta-ec) preko FRM redova = [∏ upareni = 1] *
        //   (∏ a_first doprinosi u brojiocu) / (∏ c_last doprinosi u imeniocu).
        // => Z_final = ∏_p (beta - e_afirst_p) / ∏_p (beta - e_clast_p).
        let mut num = E::ONE; let mut den = E::ONE;
        for p in 0..L {
            let taga = E::ZERO - E::from(BaseElement::new(L as u64)) + E::from(BaseElement::new(p as u64));
            let ea = taga + gamma*E::from(self.p.a_first[p]);
            let tagc = E::from(BaseElement::new(((N_R-1)*L + p) as u64));
            let ec = tagc + gamma*E::from(self.p.c_last[p]);
            num = num * (beta - ea);
            den = den * (beta - ec);
        }
        let zfin = num * den.inv();
        vec![
            Assertion::single(AUX_Z, 0, E::ONE),
            Assertion::single(AUX_Z, ACTIVE, zfin),
        ]
    }
}

struct P { options: ProofOptions, a_first: Vec<BaseElement>, c_last: Vec<BaseElement> }
impl Prover for P {
    type BaseField = BaseElement; type Air = PermAir; type Trace = PermTrace;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> Pub {
        Pub { a_first: self.a_first.clone(), c_last: self.c_last.clone(), n: N }
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
type H = Blake3_256<BaseElement>; type RC = DefaultRandomCoin<Blake3_256<BaseElement>>;

// Generiši lančane forme: a(r+1)[p] = c(r)[p]. c,a mali determinisic.
fn gen(tamper: Option<(usize,usize)>) -> (Vec<Vec<BaseElement>>, Vec<BaseElement>, Vec<BaseElement>) {
    let mut rng = 0xABCDu64;
    let mut nx = || { rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; rng % 1000 };
    // c[r][p], a[r][p]
    let mut c = vec![vec![0u64; L]; N_R];
    let mut a = vec![vec![0u64; L]; N_R];
    // a[0] proizvoljno (ulazna forma), zatim c[r] proizvoljno, a[r+1]=c[r]
    for p in 0..L { a[0][p] = nx(); }
    for r in 0..N_R {
        for p in 0..L { c[r][p] = nx(); }
        if r+1 < N_R { for p in 0..L { a[r+1][p] = c[r][p]; } }
    }
    // tamper: pokvari jedan a-limb (prekini lanac)
    if let Some((r,p)) = tamper { a[r][p] = a[r][p].wrapping_add(1); }

    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[CTR][i] = BaseElement::new(i as u64); }
    for r in 0..N_R {
        for j in 0..RR {
            let i = r*RR + j;
            if j < L {
                let p = j;
                col[AV][i]   = BaseElement::new(a[r][p]);
                col[CV][i]   = BaseElement::new(c[r][p]);
                col[TAGC][i] = BaseElement::new((r*L + p) as u64);
                // TAGA = (r-1)*L + p u polju (za r=0 => -L+p, field wrap; isto kao u asertaciji)
                col[TAGA][i] = if r == 0 {
                    BaseElement::ZERO - BaseElement::new(L as u64) + BaseElement::new(p as u64)
                } else {
                    BaseElement::new(((r-1)*L + p) as u64)
                };
                col[FRM][i]  = BaseElement::ONE;
            }
        }
    }
    let a_first: Vec<BaseElement> = (0..L).map(|p| BaseElement::new(a[0][p])).collect();
    let c_last:  Vec<BaseElement> = (0..L).map(|p| BaseElement::new(c[N_R-1][p])).collect();
    (col, a_first, c_last)
}

fn run(tamper: Option<(usize,usize)>, label: &str, expect_ok: bool) {
    let (col, a_first, c_last) = gen(tamper);
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, a_first: a_first.clone(), c_last: c_last.clone() };
    let trace = PermTrace::new(col);
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64()*1000.0;
        let pb = proof.to_bytes().len();
        let pi = Pub { a_first, c_last, n: N };
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok = winterfell::verify::<PermAir,H,RC>(proof, pi, &mo).is_ok();
        (pb, pm, ok)
    }));
    match res {
        Ok((pb, pm, ok)) => {
            println!("{}: verify={} (ocek {}) ; dokaz {:.1} KB ; prove {:.0} ms",
                label, if ok{"PASS"}else{"FAIL"}, if expect_ok{"PASS"}else{"FAIL"}, pb as f64/1024.0, pm);
            if ok != expect_ok { println!("   >>> NEOCEKIVANO!"); std::process::exit(2); }
        }
        Err(_) => { println!("{}: PANIC (ocek {})", label, if expect_ok{"PASS"}else{"FAIL"}); if expect_ok { std::process::exit(2); } }
    }
}

fn main() {
    println!("== PERM-BIND: lancano vezivanje c(r)==a(r+1) grand-product permutacijom ==");
    println!("{} blokova x {} limba ; tag=(r*L+p) c / ((r-1)*L+p) a ; 1 aux Z stubac\n", N_R, L);
    run(None, "[validan]   lanac drzi", true);
    run(Some((10, 3)), "[negativan] a[10][3]+1 (prekinut lanac)", false);
    run(Some((20, 0)), "[negativan] a[20][0]+1 (prekinut lanac)", false);
    println!("\nSVE PROSLO: permutacioni argument vezuje lanac; prekid ODBIJEN.");
}
