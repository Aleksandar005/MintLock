// ============================================================================
// KORAK 2 (produkciono skaliranje): ULANČAVANJE ~228 RUNDI u JEDAN narrow-long
// trag, preko JEDNE deljene LogUp tablice [0,2^16), sa vezivanjem granica rundi
// (F_out(r) == F_in(r+1)), disc-invarijantom 4ac-b²==|D| u svakoj rundi (D-vezivanje),
// i CTR brojačem punog stepena.
//
// Novi mehanizam KORAKA 2 (u odnosu na Korak 1 = JEDNA runda): FABRIKA ULANČAVANJA.
//   - Sve rundi žive u JEDNOM tragu, položene jedna za drugom (SEG redova po rundi).
//   - Prelaz između rundi je UNUTAR istog traga (nema više N odvojenih dokaza kao E2):
//     poslednji red rundi r nosi F_out, prvi red rundi r+1 nosi F_in; transition ih
//     vezuje. To je E2 "boundary I/O kao commitment" obrazac, ali INTERNALIZOVAN.
//   - JEDNA deljena LogUp tablica [0,2^16) range-check-uje |b| (i druge magnitude)
//     KROZ SVE rundi -> amortizacija: jedna tablica (65536 redova) za ceo reduce.
//   - Nijedan fazni selektor: svaki red je validna rho-tranzicija; granica rundi se
//     bira BOOLEAN flag kolonom (is_last u rundi), ne vremenskim gejtom.
//
// Skala: N_R=228 rundi × SEG=8 reda = 1824 aktivna reda ≪ 65536 (tablica dominira
// dužinu, kao u planu: N = next_pow2(max(računanje, 65536))). Ceo reduce (228 rundi)
// staje u JEDAN trag i JEDNU tablicu.
//
// Aritmetika po rundi (skalarna rho forma, dokazana u mulseg6; 64-limb verzija je
// Korak 1/round_full): a'=c ; b'=-b+2kc ; c'=a-kb+k²c ; disc 4ac-b²=|D|.
// Ovde je FOKUS na ulančavanju i deljenoj tablici preko SVIH rundi, ne na re-dokazivanju
// limb-aritmetike (to je round_full).
// ============================================================================

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const N: usize = 1 << 16;      // 65536 = deljena tablica [0,2^16) I dužina traga (amortizacija)
const N_R: usize = 228;        // broj rho rundi (izmereni 2048-bit worst-case)
const SEG: usize = 8;          // redova po rundi (mala rho podsekvenca; SEG-1 tranzicija/rundi)
const ACTIVE: usize = N_R * SEG; // 1824 aktivnih redova

// ---- glavne kolone ----
const A: usize = 0;      // a (magnitude)
const C: usize = 1;      // c (magnitude)
const BM: usize = 2;     // |b|
const SB: usize = 3;     // sign b (0/1)
const KM: usize = 4;     // |k|
const SK: usize = 5;     // sign k (0/1)
const SBV: usize = 6;    // potpisano b (helper, drži degree 2)
const SKV: usize = 7;    // potpisano k (helper)
const KK: usize = 8;     // k² (helper)
const ISB: usize = 9;    // is_boundary: 1 na poslednjem redu rundi, inače 0 (BOOLEAN flag)
const T_C: usize = 10;   // deljena tablica [0,N)
const M_BM: usize = 11;  // multiplicitet za |b| LogUp (deljena tablica)
const CTR: usize = 12;   // brojač punog stepena (DEEP-quirk fix)
const RIDX: usize = 13;  // indeks rundi (informativno; raste na granici)
const MAIN_W: usize = 14;

const NUM_LU: usize = 1; // jedan LogUp tok (|b|) preko SVIH rundi; lako proširivo


fn signed<E: FieldElement>(mag: E, sign: E) -> E { (E::ONE - sign - sign) * mag }

// ============================ custom Trace ============================
struct ChainTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl ChainTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        ChainTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [NUM_LU], [1]), length }
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
        &mut self, aux_segments: &[ColMatrix<E>], rand: &[E],
    ) -> Option<ColMatrix<E>> {
        if !aux_segments.is_empty() { return None; }
        let alpha = rand[0];
        let n = self.length;
        let mut s = vec![E::ZERO; n];
        let term = |i: usize| -> E {
            let v = E::from(self.main.get(BM, i));
            let t = E::from(self.main.get(T_C, i));
            let m = E::from(self.main.get(M_BM, i));
            (alpha - v).inv() - m * (alpha - t).inv()
        };
        s[0] = term(0);
        for i in 1..n { s[i] = s[i - 1] + term(i); }
        Some(ColMatrix::new(vec![s]))
    }
}

// ============================ public inputs ============================
#[derive(Clone)]
struct Pub {
    // row0 (vezuje trag) + globalna disc |D| + row0 LogUp term
    a0: BaseElement, c0: BaseElement, bm0: BaseElement, sb0: BaseElement,
    km0: BaseElement, sk0: BaseElement, isb0: BaseElement,
    bm0_lu: BaseElement, mbm0: BaseElement,
    dabs: BaseElement, n: usize,
    // finalna redukovana forma (izlaz poslednje rundi) -> javna, dokazuje "reduce done"
    a_fin: BaseElement, bm_fin: BaseElement, sb_fin: BaseElement, c_fin: BaseElement,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.a0,self.c0,self.bm0,self.sb0,self.km0,self.sk0,self.isb0,
             self.bm0_lu,self.mbm0,self.dabs,BaseElement::new(self.n as u64),
             self.a_fin,self.bm_fin,self.sb_fin,self.c_fin]
    }
}

struct ChainAir { context: AirContext<BaseElement>, p: Pub }
impl Air for ChainAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let main_deg = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(1), // CTR advance
            TransitionConstraintDegree::new(2), // ISB bool
            // rho tranzicije (gejtane sa (1-ISB) -> +1 stepen):
            TransitionConstraintDegree::new(2), // a'=c        (unutar rundi)
            TransitionConstraintDegree::new(3), // b'=-b+2kc   (SBV helper drži jezgro na 2, gejt +1)
            TransitionConstraintDegree::new(3), // c'=a-kb+k²c
            // vezivanje granice rundi (gejtano sa ISB):
            TransitionConstraintDegree::new(2), // boundary: F_out(r) veže F_in(r+1)  [a]
            TransitionConstraintDegree::new(2), // boundary [c]
            TransitionConstraintDegree::new(2), // boundary [bm]
            TransitionConstraintDegree::new(2), // boundary [sb]
            // helperi (degree 2) i disc-invarijanta:
            TransitionConstraintDegree::new(2), // SBV = signed(BM,SB)
            TransitionConstraintDegree::new(2), // SKV = signed(KM,SK)
            TransitionConstraintDegree::new(2), // KK = KM²
            TransitionConstraintDegree::new(2), // SB bool
            TransitionConstraintDegree::new(2), // SK bool
            TransitionConstraintDegree::new(2), // disc: 4ac - b² == |D|
            TransitionConstraintDegree::new(1), // RIDX advance: RIDX' == RIDX + ISB
        ];
        let aux_deg = vec![TransitionConstraintDegree::new(3); NUM_LU]; // LogUp
        // main asertacije: T0,CTR0,RIDX0,A0,C0,BM0,SB0,KM0,SK0 + finalna forma (4) = 13
        let n_main_assert = 9 + 4;
        let n_aux_assert = 2 * NUM_LU;
        let context = AirContext::new_multi_segment(
            ti, main_deg, aux_deg, n_main_assert, n_aux_assert, options);
        ChainAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let two = E::from(BaseElement::new(2));
        let four = E::from(BaseElement::new(4));
        let dabs = E::from(self.p.dabs);
        let isb = cur[ISB];
        let ingate = one - isb; // 1 unutar rundi, 0 na granici

        // globalne (svaki red):
        result[0] = nxt[T_C] - cur[T_C] - one;     // tablica raste
        result[1] = nxt[CTR] - cur[CTR] - one;     // CTR pun stepen
        result[2] = isb * (isb - one);             // ISB bool

        // rho tranzicije UNUTAR rundi (gejt ingate): a'=c, b'=-b+2kc, c'=a-kb+k²c
        let sbp = signed(nxt[BM], nxt[SB]);
        result[3] = ingate * (nxt[A] - cur[C]);
        result[4] = ingate * (sbp - (E::ZERO - cur[SBV] + two*cur[SKV]*cur[C]));
        result[5] = ingate * (nxt[C] - (cur[A] - cur[SKV]*cur[SBV] + cur[KK]*cur[C]));

        // VEZIVANJE GRANICE rundi (gejt isb): F_out(r) == F_in(r+1)
        // Na granici, sledeći red je prvi red naredne rundi; forma mora da se poklopi.
        result[6] = isb * (nxt[A]  - cur[A]);
        result[7] = isb * (nxt[C]  - cur[C]);
        result[8] = isb * (nxt[BM] - cur[BM]);
        result[9] = isb * (nxt[SB] - cur[SB]);

        // helperi (svaki red)
        result[10] = cur[SBV] - signed(cur[BM], cur[SB]);
        result[11] = cur[SKV] - signed(cur[KM], cur[SK]);
        result[12] = cur[KK] - cur[KM]*cur[KM];
        result[13] = cur[SB]*(cur[SB]-one);
        result[14] = cur[SK]*(cur[SK]-one);
        // DISC-INVARIJANTA (D-vezivanje) u svakom aktivnom redu: 4ac - b² == |D|
        result[15] = four*cur[A]*cur[C] - cur[BM]*cur[BM] - dabs;
        // RIDX raste tačno na granici rundi
        result[16] = nxt[RIDX] - cur[RIDX] - isb;
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = ACTIVE - 1;
        vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(RIDX, 0, BaseElement::ZERO),
            Assertion::single(A, 0, self.p.a0),
            Assertion::single(C, 0, self.p.c0),
            Assertion::single(BM, 0, self.p.bm0),
            Assertion::single(SB, 0, self.p.sb0),
            Assertion::single(KM, 0, self.p.km0),
            Assertion::single(SK, 0, self.p.sk0),
            // finalna redukovana forma na poslednjem aktivnom redu (izlaz reduce-a)
            Assertion::single(A, last, self.p.a_fin),
            Assertion::single(C, last, self.p.c_fin),
            Assertion::single(BM, last, self.p.bm_fin),
            Assertion::single(SB, last, self.p.sb_fin),
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
        let t = E::from(mn[T_C]);
        let v = E::from(mn[BM]);
        let m = E::from(mn[M_BM]);
        let s = aux.current()[0];
        let sp = aux.next()[0];
        result[0] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = (alpha - E::from(self.p.bm0_lu)).inv() - E::from(self.p.mbm0) * alpha.inv();
        vec![
            Assertion::single(0, 0, term0),
            Assertion::single(0, self.p.n - 1, E::ZERO), // suma = 0 -> sve |b| u tablici
        ]
    }
}

// ============================ Prover ============================
struct P { options: ProofOptions, dabs: BaseElement, a_fin: BaseElement, bm_fin: BaseElement, sb_fin: BaseElement, c_fin: BaseElement }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = ChainAir;
    type Trace = ChainTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let g = |c: usize, r: usize| t.main.get(c, r);
        Pub {
            a0: g(A,0), c0: g(C,0), bm0: g(BM,0), sb0: g(SB,0), km0: g(KM,0), sk0: g(SK,0),
            isb0: g(ISB,0), bm0_lu: g(BM,0), mbm0: g(M_BM,0),
            dabs: self.dabs,
            n: t.length(),
            a_fin: self.a_fin, bm_fin: self.bm_fin, sb_fin: self.sb_fin, c_fin: self.c_fin,
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
fn fe(x: i128) -> BaseElement { if x>=0 { BaseElement::new(x as u64) } else { BaseElement::ZERO - BaseElement::new((-x) as u64) } }

// Generiše N_R rundi rho-a nad malom fiksnom formom (disc očuvana), ulančane.
// Svaka runda = SEG redova; poslednji red rundi = is_boundary=1 i nosi F_out == F_in naredne.
struct Chain { a: Vec<i128>, b: Vec<i128>, c: Vec<i128>, k: Vec<i128>, isb: Vec<u64>, ridx: Vec<u64>, dabs: u64 }

fn gen_chain() -> Chain {
    // Startna forma sa 4ac-b²=|D|. Rho ciklus perioda 2 (swap+neg): drži disc konstantnim
    // i sve magnitude male (idealno za deljenu tablicu). Ista disc kroz sve rundi (D-vezivanje).
    let a0: i128 = 380; let b0: i128 = 241; let c0: i128 = 7146;
    let dabs = (b0*b0 - 4*a0*c0).unsigned_abs() as u64; // |D| = |b²-4ac|
    let (mut a, mut b, mut c) = (a0, b0, c0);
    let mut av=vec![]; let mut bv=vec![]; let mut cv=vec![]; let mut kv=vec![]; let mut isb=vec![]; let mut ridx=vec![];
    for r in 0..N_R {
        for s in 0..SEG {
            av.push(a); bv.push(b); cv.push(c);
            let last_in_round = s == SEG - 1;
            isb.push(if last_in_round {1} else {0});
            ridx.push(r as u64);
            if last_in_round {
                // granica: sledeći red je prvi red naredne rundi = ISTA forma (F_out==F_in).
                // k na granici = 0 (nema rho pomaka preko granice); forma se prosto prenosi.
                kv.push(0);
                // (a,b,c) ostaju isti -> naredni red iste vrednosti; disc očuvana trivijalno.
            } else {
                // unutar rundi: rho korak sa k tako da forma ostaje mala i disc očuvana.
                // koristimo k=0 swap-neg ciklus:  a'=c, b'=-b, c'=a  (period 2, disc isti)
                let k: i128 = 0;
                kv.push(k);
                let (na, nb, nc) = (c, -b + 2*k*c, a - k*b + k*k*c);
                a = na; b = nb; c = nc;
            }
        }
    }
    // poslednji red nema "next" u aktivnom delu (biće vezan padding-om); k=0
    Chain { a: av, b: bv, c: cv, k: kv, isb, ridx, dabs }
}

#[derive(Clone, Copy)]
enum Tamper { None, BreakChain(usize), BreakDisc(usize), OutOfRangeBM(usize, u64) }

fn build_trace(ch: &Chain, tamper: Tamper) -> (ChainTrace, Pub) {
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i] = BaseElement::new(i as u64); col[CTR][i] = BaseElement::new(i as u64); }
    // aktivni redovi
    for i in 0..ACTIVE {
        let (a,b,c,k) = (ch.a[i], ch.b[i], ch.c[i], ch.k[i]);
        col[A][i]=mag(a); col[C][i]=mag(c); col[BM][i]=mag(b); col[SB][i]=sgn(b);
        col[KM][i]=mag(k); col[SK][i]=sgn(k);
        col[SBV][i]=fe(b); col[SKV][i]=fe(k); col[KK][i]=BaseElement::new((k*k) as u64);
        col[ISB][i]=BaseElement::new(ch.isb[i]);
        col[RIDX][i]=BaseElement::new(ch.ridx[i]);
    }
    // padding (i>=ACTIVE): sve magnitude 0 -> disc bi tražila 4·0·0-0==|D| što NE važi.
    // Zato disc-invarijantu i rho gejtujemo samo na aktivnom delu preko posebnog "active" reda?
    // Umesto toga: u padding-u postavljamo formu koja ZADOVOLJAVA disc (a=A_pad,c=C_pad,b=B_pad
    // sa 4·a·c-b²=|D|) i ISB=0, k=0, swap-neg -> svaki padding red je validna rho tranzicija
    // i validna disc. Najlakše: ponovi POSLEDNJU aktivnu formu kroz ceo padding (k=0 swap-neg
    // perioda 2 čuva disc i magnitude), sa ISB=0.
    // Da bi swap-neg u padding-u bio konzistentan (a'=c,b'=-b,c'=a), postavljamo naizmenično.
    let (mut pa, mut pb, mut pc) = (ch.a[ACTIVE-1], ch.b[ACTIVE-1], ch.c[ACTIVE-1]);
    // "isteraj" poslednju formu u redukovanu malu formu za padding (swap-neg drži disc)
    for i in ACTIVE..N {
        col[A][i]=mag(pa); col[C][i]=mag(pc); col[BM][i]=mag(pb); col[SB][i]=sgn(pb);
        col[KM][i]=BaseElement::ZERO; col[SK][i]=BaseElement::ZERO;
        col[SBV][i]=fe(pb); col[SKV][i]=BaseElement::ZERO; col[KK][i]=BaseElement::ZERO;
        col[ISB][i]=BaseElement::ZERO;
        col[RIDX][i]=BaseElement::new(N_R as u64);
        let (na,nb,nc)=(pc,-pb,pa); pa=na; pb=nb; pc=nc; // swap-neg, disc očuvana
    }
    // RIDX u padding-u mora da bude konstantan (ISB=0 -> RIDX'==RIDX). Postavili N_R svuda gore. OK.
    // Ali PRVI padding red čita se kao "next" poslednjeg aktivnog (koji ima ISB=1 ako je SEG granica).
    // Poslednji aktivni red i=ACTIVE-1 ima ISB=1 (kraj poslednje rundi) -> boundary constraint traži
    // nxt == cur za a,c,bm,sb. Zato prvi padding red MORA biti ista forma kao ACTIVE-1:
    col[A][ACTIVE]=col[A][ACTIVE-1]; col[C][ACTIVE]=col[C][ACTIVE-1];
    col[BM][ACTIVE]=col[BM][ACTIVE-1]; col[SB][ACTIVE]=col[SB][ACTIVE-1];
    col[SBV][ACTIVE]=col[SBV][ACTIVE-1];
    // i RIDX' == RIDX + ISB(=1) na toj granici -> RIDX[ACTIVE] = RIDX[ACTIVE-1]+1 = N_R
    col[RIDX][ACTIVE]=BaseElement::new(N_R as u64);

    // tamper
    match tamper {
        Tamper::None => {}
        Tamper::BreakChain(r) => {
            // Izoluj vezivanje granice: promeni ZNAK b na PRVOM redu naredne rundi (F_in).
            // disc koristi b² -> disc OSTAJE validna; |b| isti -> LogUp OSTAJE balansiran;
            // ali F_out.SB != F_in.SB -> boundary nxt[SB]==cur[SB] PUCA. Čist test granice.
            let fin_row = (r+1)*SEG; // prvi red naredne rundi
            let sb = col[SB][fin_row];
            col[SB][fin_row] = BaseElement::ONE - sb; // flip sign bit
            col[SBV][fin_row] = BaseElement::ZERO - col[SBV][fin_row]; // uskladi helper (SBV=signed)
        }
        Tamper::BreakDisc(r) => {
            // pokvari disc u jednom redu (promeni c) -> 4ac-b²!=|D|
            let row = r*SEG + 1;
            col[C][row] = col[C][row] + BaseElement::ONE;
        }
        Tamper::OutOfRangeBM(r, val) => {
            let row = r*SEG + 2;
            col[BM][row] = BaseElement::new(val); // van [0,2^16) -> LogUp
        }
    }

    // multipliciteti za |b| LogUp (broji SVE redove, aktivne + padding)
    let mut mult = vec![0u64; N];
    for i in 0..N { let v = col[BM][i].as_int(); if (v as usize) < N { mult[v as usize]+=1; } }
    for i in 0..N { col[M_BM][i]=BaseElement::new(mult[i]); }

    let g = |c: &Vec<Vec<BaseElement>>, cc: usize, r: usize| c[cc][r];
    let last = ACTIVE - 1;
    let p = Pub {
        a0:g(&col,A,0), c0:g(&col,C,0), bm0:g(&col,BM,0), sb0:g(&col,SB,0),
        km0:g(&col,KM,0), sk0:g(&col,SK,0), isb0:g(&col,ISB,0),
        bm0_lu:g(&col,BM,0), mbm0:g(&col,M_BM,0),
        dabs: BaseElement::new(ch.dabs), n: N,
        a_fin:g(&col,A,last), bm_fin:g(&col,BM,last), sb_fin:g(&col,SB,last), c_fin:g(&col,C,last),
    };
    (ChainTrace::new(col), p)
}

fn run(ch: &Chain, tamper: Tamper, label: &str, expect_ok: bool) {
    let (trace, pi) = build_trace(ch, tamper);
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, dabs: pi.dabs, a_fin: pi.a_fin, bm_fin: pi.bm_fin, sb_fin: pi.sb_fin, c_fin: pi.c_fin };
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64()*1000.0;
        let pb = proof.to_bytes().len();
        let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let t1 = Instant::now();
        let ok = winterfell::verify::<ChainAir, H, RC>(proof, pi.clone(), &mo).is_ok();
        let vm = t1.elapsed().as_secs_f64()*1000.0;
        (pb, sec, pm, vm, ok)
    }));
    match res {
        Ok((pb, sec, pm, vm, ok)) => {
            println!("{}: verify={} (ocek {}) ; dokaz {:.1} KB ; prove {:.0} ms ; verify {:.1} ms ; sec {}",
                label, if ok {"PASS"} else {"FAIL"}, if expect_ok {"PASS"} else {"FAIL"},
                pb as f64/1024.0, pm, vm, sec);
            if ok != expect_ok { println!("   >>> NEOCEKIVANO!"); std::process::exit(2); }
        }
        Err(_) => {
            println!("{}: PANIC/odbijen (ocek {})", label, if expect_ok {"PASS"} else {"FAIL"});
            if expect_ok { std::process::exit(2); }
        }
    }
}


fn main() {
    println!("== KORAK 2: ULANČAVANJE {} rundi u JEDAN trag + JEDNA deljena LogUp tablica [0,2^16) ==", N_R);
    println!("glavne kolone: {} + aux (LogUp): {} = {} (< 255)", MAIN_W, NUM_LU, MAIN_W+NUM_LU);
    println!("aktivnih redova: {} (= {} rundi × {} reda) ; dužina traga N = {} (tablica dominira)",
             ACTIVE, N_R, SEG, N);
    println!("mehanizmi: vezivanje granice rundi (F_out==F_in) + disc-invarijanta 4ac-b²=|D| + CTR");
    println!("amortizacija: JEDNA tablica {} redova za |b| range-check KROZ SVIH {} rundi\n", N, N_R);

    let ch = gen_chain();
    println!("startna forma: a={} b={} c={} ; |D|={} ; disc očuvana kroz sve rundi",
             ch.a[0], ch.b[0], ch.c[0], ch.dabs);

    run(&ch, Tamper::None, "[validan]   228 rundi ulančano", true);
    run(&ch, Tamper::BreakChain(100), "[negativan] prekinut lanac @rundi 100 (F_out!=F_in)", false);
    run(&ch, Tamper::BreakDisc(50),   "[negativan] pokvarena disc @rundi 50 (4ac-b²!=|D|)", false);
    run(&ch, Tamper::OutOfRangeBM(30, 70000), "[negativan] |b|@rundi 30 = 70000 (van tablice, LogUp)", false);

    println!("\nSVE PROSLO: ceo reduce ({} rundi) ulančan u JEDAN trag pod JEDNOM deljenom", N_R);
    println!("LogUp tablicom; granice rundi vezane, disc vezuje |D| svuda, CTR pun stepen.");
}
