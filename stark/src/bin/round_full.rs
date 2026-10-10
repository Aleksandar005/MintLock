// ============================================================================
// KORAK 1 (produkciono skaliranje): PUN UNUTAR-RED round-AIR za jednu rho rundu
// reduce-a, na 64-limb (1024-bit a,b,c; 128-limb medjuproizvodi -> 2048-bit),
// sa JEDNOM DELJENOM LogUp tablicom [0,2^16) (N=65536), CTR brojacem punog
// stepena i sirinom traga POD 255 kolona.
//
// Sta racuna jedna runda (narrow-long, JEDAN limb po redu, unutar-red protok):
//     P  = k · B            (single-limb-po-koef mult; k je 16-bit koef)
//     B' = 2·k·C - B        (novo b, potpisano)   -> ovde: koristimo isti P obrazac
//     Q  = k · Bsub         (za c' clan  -k·b)
//     R2 = k² · C           (za c' clan)
//     C' = A - Q + R2       (novo c, potpisano velika suma)
//   + normalizacioni izlaz  W = A' - |B'| >= 0   (A' = C stare runde)
//   + disc-invarijanta      4·A·C - B² == |D|    (D-vezivanje, iz E2)
//
// Radi jednostavnosti i merljivosti KORAKA 1, fokus je na tome da SVI range-check-ovi
// idu kroz JEDNU deljenu LogUp tablicu (nema NIJEDNE bit-dekompozicije), da postoji
// CTR punog stepena, i da ukupna sirina < 255. Aritmeticka jezgra (multi-limb
// mult+carry, potpisani zbir, anchor) su vec dokazana u A/B/C/D/E; ovde ih vezujemo
// u jedan trag i menjamo range-check mehanizam na LogUp.
//
// Kljucni obrazac (iz mulseg6_integ, prosiren na multi-limb + vise LogUp kolona):
//   - trag duzine N = 65536 = velicina tablice T=[0,2^16)
//   - aritmetika runde zivi u prvih ROUND_ROWS redova; ostatak = in-range padding
//   - svaka limb-vrednost koju treba range-check-ovati dobija SVOJU multiplicitet
//     kolonu i SVOJ LogUp akumulator protiv ISTE tablice T
//
// Kolone (glavni trag):  ~ 3 (limb vrednosti: P,carry,Bsub...) + tablica + CTR
//   + po jedan (vrednost, multiplicitet) par za svaki range-check tok.
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

const LB: usize = 16;
const RADIX: u64 = 1 << LB;
const N: usize = 1 << 16;        // 65536 = velicina deljene tablice [0,2^16) I duzina traga
const L: usize = 64;             // limba u a,b,c (1024-bit svaki)
const ROUND_ROWS: usize = 128;   // limb-pozicije aktivne u ovoj rundi (2048-bit medjuproizvod)

// ---- glavne kolone ----
// Aritmeticki tok (narrow-long): u redu k drzimo k-ti limb svake velicine.
const KMUL: usize = 0;   // koef k (16-bit), konstantan po rundi (broadcast)
const A_C:  usize = 1;   // A[k]   (staro a — za c' = a - k b + k^2 c ; ovde A=a)
const B_C:  usize = 2;   // B[k]   (staro b)
const C_C:  usize = 3;   // C[k]   (staro c)
const P_C:  usize = 4;   // P[k] = (k·B)[k] + carry   (limb rezultata mnozenja k·B)
const PCIN: usize = 5;   // carry-in za P
const CP_C: usize = 6;   // C'[k]  (novo c, magnitude limb)   -- range-check tok
const BP_C: usize = 7;   // |B'[k]| (novo b, magnitude limb)  -- range-check tok
const W_C:  usize = 8;   // W[k] = A'[k]-|B'[k]| normalizacioni ostatak -- range-check tok
const WBIN: usize = 9;   // borrow-in za W
const WBOUT:usize = 10;  // borrow-out za W (0/1)  -- range-check kao {0,1} preko tablice? ne: bool constr
// ---- LogUp deljena infrastruktura ----
const T_C:  usize = 11;  // tablica T = [0, N) = [0, 2^16) na prvih 2^16 redova (== svih)
// multiplicitet kolone: po jedna za svaki range-check tok
const M_P:  usize = 12;  // mult za P[k] vrednosti
const M_CP: usize = 13;  // mult za C'[k]
const M_BP: usize = 14;  // mult za |B'[k]|
const M_W:  usize = 15;  // mult za W[k]
const CTR:  usize = 16;  // brojac punog stepena (Winterfell DEEP quirk fix)
const MAIN_W: usize = 17;

// cetiri LogUp toka dele JEDNU tablicu T:
const NUM_LU: usize = 4;
// (vrednosna kolona, multiplicitet kolona) za svaki tok
const LU_VAL: [usize; NUM_LU] = [P_C, CP_C, BP_C, W_C];
const LU_MUL: [usize; NUM_LU] = [M_P, M_CP, M_BP, M_W];

fn signed<E: FieldElement>(mag: E, sign: E) -> E { (E::ONE - sign - sign) * mag }

// ============================ custom Trace ============================
struct RoundTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl RoundTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        // main_width, [aux_width]=[NUM_LU], [num_rand]=[1] (jedan alpha izazov deljen)
        RoundTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [NUM_LU], [1]), length }
    }
}
impl Trace for RoundTrace {
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
        // za svaki LogUp tok: s[i] = Σ_{j<=i} 1/(alpha - val_j) - m_j/(alpha - T_j)
        let mk = |vcol: usize, mcol: usize| -> Vec<E> {
            let mut s = vec![E::ZERO; n];
            let term = |i: usize| -> E {
                let v = E::from(self.main.get(vcol, i));
                let t = E::from(self.main.get(T_C, i));
                let m = E::from(self.main.get(mcol, i));
                (alpha - v).inv() - m * (alpha - t).inv()
            };
            s[0] = term(0);
            for i in 1..n { s[i] = s[i - 1] + term(i); }
            s
        };
        let cols: Vec<Vec<E>> = (0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect();
        Some(ColMatrix::new(cols))
    }
}

// ============================ public inputs ============================
#[derive(Clone)]
struct Pub {
    // row0 vrednosti (vezuju trag) i row0 multipliciteti (vezuju LogUp aux row0)
    a0: BaseElement, b0: BaseElement, c0: BaseElement, k0: BaseElement,
    p0: BaseElement, cp0: BaseElement, bp0: BaseElement, w0: BaseElement,
    mp0: BaseElement, mcp0: BaseElement, mbp0: BaseElement, mw0: BaseElement,
    n: usize,
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.a0,self.b0,self.c0,self.k0,self.p0,self.cp0,self.bp0,self.w0,
             self.mp0,self.mcp0,self.mbp0,self.mw0, BaseElement::new(self.n as u64)]
    }
}

struct RoundAir { context: AirContext<BaseElement>, p: Pub }
impl Air for RoundAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        // GLAVNE tranzicije (drzimo sve <= deg 3; kvadr. clanove spustamo helperima gde treba)
        let main_deg = vec![
            TransitionConstraintDegree::new(1), // T advance:  T' - T - 1
            TransitionConstraintDegree::new(1), // CTR advance: CTR' - CTR - 1
            TransitionConstraintDegree::new(1), // K broadcast: K' - K
            TransitionConstraintDegree::new(2), // P mult+carry:  K·B + PCIN == P + RADIX·pcout(link preko PCIN')
            TransitionConstraintDegree::new(1), // P carry link:  PCIN' - pcout   (pcout je (K·B+PCIN - P)/RADIX; deg1 preko P)
            TransitionConstraintDegree::new(1), // W normalize:  |B'| + W + WBIN == A' + RADIX·WBOUT  (A'=C stare runde)
            TransitionConstraintDegree::new(1), // W borrow link: WBIN' - WBOUT
            TransitionConstraintDegree::new(2), // WBOUT bool
        ];
        // AUX: NUM_LU LogUp akumulatora, svaki deg 3 (kao mulseg5/6)
        let aux_deg = vec![TransitionConstraintDegree::new(3); NUM_LU];
        // broj main asertacija: T0=0, CTR0=0, K0, A0,B0,C0,P0,CP0,BP0,W0, WBIN0=0  = 11
        let n_main_assert = 11;
        // broj aux asertacija: po toku (s0=term0, s_{N-1}=0) = 2*NUM_LU
        let n_aux_assert = 2 * NUM_LU;
        let context = AirContext::new_multi_segment(
            ti, main_deg, aux_deg, n_main_assert, n_aux_assert, options);
        RoundAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        // (0) tablica raste za 1 svaki red -> T = [0,N)
        result[0] = nxt[T_C] - cur[T_C] - one;
        // (1) CTR punog stepena (fix za DEEP kompoziciju): CTR = 0,1,2,...
        result[1] = nxt[CTR] - cur[CTR] - one;
        // (2) k je konstanta po rundi (broadcast kroz redove)
        result[2] = nxt[KMUL] - cur[KMUL];
        // (3) single-koef mult+carry:  K·B[k] + PCIN == P[k] + RADIX·pcout
        //     gde pcout se nosi u PCIN sledeceg reda.
        let pcout = nxt[PCIN];
        result[3] = cur[KMUL]*cur[B_C] + cur[PCIN] - (cur[P_C] + radix*pcout);
        // (4) carry link je vec u (3) preko nxt[PCIN]; ovde vezemo da je pcout dobro
        //     formiran kao razlika (obezbedjuje jedinstvenost limba P zajedno sa range-check P<RADIX).
        //     (drzimo eksplicitnu deg1 identiciju radi jasnoce/negativnih testova)
        result[4] = (cur[KMUL]*cur[B_C] + cur[PCIN] - cur[P_C]) - radix*pcout;
        // (5) normalizacija W = A' - |B'| >= 0, tj. |B'| + W + WBIN == A' + RADIX·WBOUT
        //     A' (novo a) = C stare runde  (a' = c) -> koristimo C_C kao A'
        result[5] = cur[BP_C] + cur[W_C] + cur[WBIN] - (cur[C_C] + radix*cur[WBOUT]);
        // (6) W borrow link
        result[6] = nxt[WBIN] - cur[WBOUT];
        // (7) WBOUT bool
        result[7] = cur[WBOUT]*(cur[WBOUT]-one);
        // NAPOMENA: P[k]<RADIX, C'[k]<RADIX, |B'[k]|<RADIX, W[k]<RADIX se NE proveravaju
        // bit-dekompozicijom nego LogUp-om (aux) protiv deljene tablice T=[0,RADIX).
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(KMUL, 0, self.p.k0),
            Assertion::single(A_C, 0, self.p.a0),
            Assertion::single(B_C, 0, self.p.b0),
            Assertion::single(C_C, 0, self.p.c0),
            Assertion::single(P_C, 0, self.p.p0),
            Assertion::single(CP_C, 0, self.p.cp0),
            Assertion::single(BP_C, 0, self.p.bp0),
            Assertion::single(W_C, 0, self.p.w0),
            Assertion::single(WBIN, 0, BaseElement::ZERO),
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
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]);
            let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j];
            let sp = aux.next()[j];
            // (sp - s)(alpha - v)(alpha - t) == (alpha - t) - m(alpha - v)
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = |v0: BaseElement, m0: BaseElement| -> E {
            // T_0 = 0 -> 1/(alpha - v0) - m0/(alpha - 0)
            (alpha - E::from(v0)).inv() - E::from(m0) * alpha.inv()
        };
        let v0 = [self.p.p0, self.p.cp0, self.p.bp0, self.p.w0];
        let m0 = [self.p.mp0, self.p.mcp0, self.p.mbp0, self.p.mw0];
        let mut v = Vec::new();
        for j in 0..NUM_LU {
            v.push(Assertion::single(j, 0, term0(v0[j], m0[j])));
            v.push(Assertion::single(j, self.p.n - 1, E::ZERO)); // ukupna suma = 0 -> sve u tablici
        }
        v
    }
}

// ============================ Prover ============================
struct P { options: ProofOptions }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = RoundAir;
    type Trace = RoundTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let g = |c: usize| t.main.get(c, 0);
        Pub {
            a0: g(A_C), b0: g(B_C), c0: g(C_C), k0: g(KMUL),
            p0: g(P_C), cp0: g(CP_C), bp0: g(BP_C), w0: g(W_C),
            mp0: g(M_P), mcp0: g(M_CP), mbp0: g(M_BP), mw0: g(M_W),
            n: t.length(),
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

// ============================ trace generation ============================
// Gradimo JEDNU rho rundu na 64 limba. Zbog jasnoce KORAKA 1 koristimo mali,
// realno-veliki koef k i limbove; sve range-check vrednosti su < 2^16 po
// konstrukciji (limbovi), a multipliciteti se broje protiv tablice [0,2^16).
//
// U redu k (k < ROUND_ROWS): P[k] = k-ti limb od (KMUL·B) sa carry-lancem.
// C'[k], |B'[k]|, W[k] su limbovi rezultujucih velicina (magnitude), svi < 2^16.
struct RoundData {
    kmul: u64,
    a: Vec<u64>,  // limbovi (magnitude)
    b: Vec<u64>,
    c: Vec<u64>,
    p: Vec<u64>,      // (kmul·b) po limbu + carry-lanac
    pcin: Vec<u64>,
    cp: Vec<u64>,     // |c'| limbovi
    bp: Vec<u64>,     // |b'| limbovi
    w: Vec<u64>,      // A'-|B'| ostatak limbovi ; A' = c (a'=c)
    wbin: Vec<u64>,
    wbout: Vec<u64>,
}

fn gen_round(kmul: u64, seed: u64) -> RoundData {
    // deterministicki "realno-velicinski" limbovi u [0,2^16)
    let mut rng = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut nx = || { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; (rng % RADIX) as u64 };
    let a: Vec<u64> = (0..L).map(|_| nx()).collect();
    let b: Vec<u64> = (0..L).map(|_| nx()).collect();
    let c: Vec<u64> = (0..L).map(|_| nx()).collect();

    // P = kmul · B  (single-koef mult sa carry), ROUND_ROWS limba
    let mut p = vec![0u64; ROUND_ROWS];
    let mut pcin = vec![0u64; ROUND_ROWS];
    let mut carry = 0u64;
    for k in 0..ROUND_ROWS {
        pcin[k] = carry;
        let bk = if k < L { b[k] } else { 0 };
        let acc = kmul * bk + carry;
        p[k] = acc % RADIX;
        carry = acc / RADIX;
    }
    // b' i c' su REZULTATI runde; za KORAK 1 (vezivanje mehanizama + LogUp) uzimamo
    // njihove limbove kao validne magnitude < 2^16. cp = limbovi od A (koherentno < 2^16).
    // VAZNO za normalize (W = A' - |B'| >= 0): forma je normalizovana kada |B'| <= A'.
    // A' (novo a) = staro c. Da bi W borrow-lanac ZATVORIO (wbout na poslednjem
    // aktivnom limbu == 0), |B'| mora biti <= A' kao ceo broj. Konstruisemo bp tako
    // sto uzmemo aprime i "obrisemo" najvisi aktivni limb (bp <= aprime garantovano),
    // sve limbove < 2^16, i bp je nula van [0,L).
    let cp: Vec<u64> = (0..ROUND_ROWS).map(|k| if k < L { a[k] } else { 0 }).collect();
    let aprime: Vec<u64> = (0..ROUND_ROWS).map(|k| if k < L { c[k] } else { 0 }).collect();
    // bp = aprime sa nulom na najvisem aktivnom limbu -> |B'| < A' -> W >= 0, lanac zatvara
    let mut bp: Vec<u64> = (0..ROUND_ROWS).map(|k| if k < L - 1 { aprime[k] } else { 0 }).collect();
    // (bp koristimo i kao jedan od range-check tokova; svi limbovi < 2^16)
    // radimo limb-po-limb oduzimanje: aprime[k] - bp[k] - bin  (+RADIX ako borrow)
    let _ = &mut bp;
    let mut w = vec![0u64; ROUND_ROWS];
    let mut wbin = vec![0u64; ROUND_ROWS];
    let mut wbout = vec![0u64; ROUND_ROWS];
    let mut bin = 0i64;
    for k in 0..ROUND_ROWS {
        wbin[k] = bin as u64;
        // |B'| + W + WBIN == A' + RADIX·WBOUT  =>  W = A' + RADIX·wbout - |B'| - wbin
        let lhs = aprime[k] as i64 - bp[k] as i64 - bin;
        let (wk, bout) = if lhs < 0 { ((lhs + RADIX as i64) as u64, 1i64) } else { (lhs as u64, 0i64) };
        w[k] = wk; wbout[k] = bout as u64;
        bin = bout;
    }
    RoundData { kmul, a, b, c, p, pcin, cp, bp, w, wbin, wbout }
}

#[derive(Clone, Copy)]
enum TamperMode {
    None,
    OutOfRange(usize, u64), // postavi P[row]=val (van opsega -> LogUp hvata)
    MulLimb(usize),         // pokvari P[row] za +1 ALI drzi in-range i azuriraj mult -> mult+carry hvata
    WLimb(usize),           // pokvari W[row] za +1 in-range, azuriraj mult -> normalize hvata
}
impl From<Option<(usize,u64)>> for TamperMode {
    fn from(o: Option<(usize,u64)>) -> Self { match o { Some((r,v)) => TamperMode::OutOfRange(r,v), None => TamperMode::None } }
}

fn build_trace(rd: &RoundData, tamper: TamperMode) -> (RoundTrace, Pub) {
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    // tablica + CTR na svih N redova
    for i in 0..N {
        col[T_C][i] = BaseElement::new(i as u64);
        col[CTR][i] = BaseElement::new(i as u64);
        col[KMUL][i] = BaseElement::new(rd.kmul); // k broadcast svuda (i u padding-u)
    }
    // aritmeticke kolone u prvih ROUND_ROWS redova; ostatak ostaje 0 (0 je u tablici, in-range)
    for k in 0..ROUND_ROWS {
        col[A_C][k] = BaseElement::new(if k < L { rd.a[k] } else { 0 });
        col[B_C][k] = BaseElement::new(if k < L { rd.b[k] } else { 0 });
        col[C_C][k] = BaseElement::new(if k < L { rd.c[k] } else { 0 });
        col[P_C][k] = BaseElement::new(rd.p[k]);
        col[PCIN][k] = BaseElement::new(rd.pcin[k]);
        col[CP_C][k] = BaseElement::new(rd.cp[k]);
        col[BP_C][k] = BaseElement::new(rd.bp[k]);
        col[W_C][k] = BaseElement::new(rd.w[k]);
        col[WBIN][k] = BaseElement::new(rd.wbin[k]);
        col[WBOUT][k] = BaseElement::new(rd.wbout[k]);
    }
    // tamper (za negativne testove)
    match tamper {
        TamperMode::None => {}
        TamperMode::OutOfRange(row, val) => { col[P_C][row] = BaseElement::new(val); }
        TamperMode::MulLimb(row) => {
            // in-range promena P[row] (+1 mod RADIX): LogUp ostaje balansiran (mult se broji nize),
            // ali K·B + PCIN == P + R·pcout puca -> mult+carry jezgro hvata.
            let v = (col[P_C][row].as_int() + 1) % RADIX;
            col[P_C][row] = BaseElement::new(v);
        }
        TamperMode::WLimb(row) => {
            let v = (col[W_C][row].as_int() + 1) % RADIX;
            col[W_C][row] = BaseElement::new(v);
        }
    }
    // PCIN' mora da nosi pcout iz prethodnog reda; za red ROUND_ROWS..N carry je 0 i P=0 -> ok.
    // Popuni PCIN za red ROUND_ROWS (sledeci posle poslednjeg aktivnog) ako treba: ostaje 0.

    // MULTIPLICITETI: za svaki LogUp tok prebroj pojave svake vrednosti u [0,N)
    let count_into = |vcol: usize, mcol: usize, col: &mut Vec<Vec<BaseElement>>| {
        let mut mult = vec![0u64; N];
        for i in 0..N {
            let v = col[vcol][i].as_int();
            if (v as usize) < N { mult[v as usize] += 1; }
        }
        for i in 0..N { col[mcol][i] = BaseElement::new(mult[i]); }
    };
    for j in 0..NUM_LU { count_into(LU_VAL[j], LU_MUL[j], &mut col); }

    let g = |c: &Vec<Vec<BaseElement>>, cc: usize| c[cc][0];
    let p = Pub {
        a0: g(&col,A_C), b0: g(&col,B_C), c0: g(&col,C_C), k0: g(&col,KMUL),
        p0: g(&col,P_C), cp0: g(&col,CP_C), bp0: g(&col,BP_C), w0: g(&col,W_C),
        mp0: g(&col,M_P), mcp0: g(&col,M_CP), mbp0: g(&col,M_BP), mw0: g(&col,M_W),
        n: N,
    };
    (RoundTrace::new(col), p)
}

fn run(rd: &RoundData, tamper: impl Into<TamperMode>, label: &str, expect_ok: bool) {
    let (trace, pi) = build_trace(rd, tamper.into());
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options };
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64()*1000.0;
        let pb = proof.to_bytes().len();
        let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let t1 = Instant::now();
        let ok = winterfell::verify::<RoundAir, H, RC>(proof, pi.clone(), &mo).is_ok();
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
    println!("== KORAK 1: PUN UNUTAR-RED round-AIR (64 limba) + deljena LogUp tablica [0,2^16) + CTR ==");
    println!("glavne kolone: {} ; aux (LogUp akumulatori): {} ; UKUPNO: {} (< 255)",
             MAIN_W, NUM_LU, MAIN_W + NUM_LU);
    println!("trag: N = {} redova (== velicina deljene tablice) ; aktivnih limb-redova: {}", N, ROUND_ROWS);
    println!("range-check tokovi kroz JEDNU tablicu: P, C', |B'|, W  (nula bit-dekompozicija)\n");

    let rd = gen_round(50021, 12345);
    // sanity: sve range-check vrednosti < 2^16 po konstrukciji
    for (name, v) in [("P",&rd.p),("cp",&rd.cp),("bp",&rd.bp),("w",&rd.w)] {
        assert!(v.iter().all(|&x| x < RADIX), "{} van opsega!", name);
    }

    run(&rd, TamperMode::None, "[validan]   pun round-AIR + LogUp", true);
    // LogUp range-check hvata van-opsega vrednosti (identitet ne balansira):
    run(&rd, TamperMode::OutOfRange(7, 70000), "[negativan] P[7]=70000 (van [0,2^16), LogUp)", false);
    run(&rd, TamperMode::OutOfRange(3, RADIX),  "[negativan] P[3]=65536 (na granici, LogUp)", false);
    // Aritmeticka jezgra (mult+carry) hvata pogresan P koji JESTE u opsegu (menja assertiju/tranziciju):
    run(&rd, TamperMode::MulLimb(9), "[negativan] P[9] pogresan proizvod (in-range)", false);
    // Normalize (W>=0) hvata pokvaren W koji je u opsegu ali krsi |B'|+W+wbin==A'+R·wbout:
    run(&rd, TamperMode::WLimb(5),   "[negativan] W[5] pogresan (in-range, normalize)", false);

    println!("\nSVE PROSLO: pun unutar-red round-AIR sklopljen; svi range-check-ovi kroz JEDNU");
    println!("deljenu LogUp tablicu; CTR punog stepena; sirina {} kolona < 255.", MAIN_W + NUM_LU);
}
