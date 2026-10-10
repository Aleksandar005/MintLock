// ============================================================================
// KORAK 3 (produkciono skaliranje): SPAJANJE Koraka 1 i 2.
// Svaka runda postaje BLOK od RR limb-redova (puna 64-limb narrow-long aritmetika
// iz round_full: P=k·B mult+carry, W normalize), a rundi su ULANČANE end-to-end
// (fabrika iz reduce_chain), sve pod JEDNOM deljenom LogUp tablicom [0,2^16).
//
// Novi (integracioni) sadržaj Koraka 3: obrazac ulančavanja iz Koraka 2 sada radi
// nad BLOKOVIMA umesto nad skalarima, a vezivanje granice rundi je POZICIONO na
// limb-nivou:  a-limbovi rundi r+1  ==  c-limbovi rundi r   (rho: a'=c), limb-po-limb.
//
// Ključni mehanizmi (svi već dokazani pojedinačno; ovde spojeni u jedan trag):
//   1. 64-limb mult+carry (P = k·B) sa carry-lancem UNUTAR bloka        [Korak 1]
//   2. normalize W = A' - |B'| >= 0 sa borrow-lancem                     [Korak 1]
//   3. SVI limb range-check-ovi kroz JEDNU deljenu LogUp tablicu         [Korak 1/2]
//   4. ulančavanje blokova: a_limbs(r+1) == c_limbs(r) na granici        [Korak 2, sada limb-poziciono]
//   5. |D| kao javni ulaz (deo transkripta; puna disc-recompozicija iz limba je
//      zaseban korak — vidi napomenu o poštenom obimu)                  [Korak 2]
//   6. CTR pun stepen (DEEP-quirk fix)                                    [Korak 1/2]
//
// Raspored redova: JEDAN limb po redu; RR redova po rundi; rundi jedna za drugom.
//   red  base_r + k   drži k-ti limb rundi r  (k = 0..RR).
// Granica rundi (poslednji limb-red rundi -> prvi limb-red naredne) nosi flag ISB.
// Poziciono vezivanje a'(r+1)[k] == c(r)[k]: pošto su i-ti limbovi rundi r i r+1
// UDALJENI za RR redova (ne susedni), koristimo POMOĆNU kolonu ACARRY koja "prenosi"
// c-limb rundi r na a-limb rundi r+1 na ISTOM limb-indeksu, verifikovano preko
// per-blok POZICIONIH asertacija (Winterfell Assertion::single na fiksnom redu).
//
// Napomena o skali: N_R rundi × RR redova mora <= N=65536. Za demonstraciju spajanja
// biramo umeren N_R tako da blok-aritmetika + tablica staju; puni 228×128=29184 < 65536
// takođe staje (vidi STATUS), ali prove vreme raste linearno sa aktivnim redovima.
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
const N: usize = 1 << 16;      // 65536 = deljena tablica [0,2^16) I dužina traga
const L: usize = 64;           // limba u a,b,c
const RR: usize = 128;         // redova (limb-pozicija) po rundi
const N_R: usize = 228;        // pun broj rundi (2048-bit worst-case)
const ACTIVE: usize = N_R * RR; // 29184 aktivnih redova

// ---- glavne kolone ----
const KMUL: usize = 0;   // koef k rundi (broadcast unutar bloka)
const A_C:  usize = 1;   // a[k]  (ulaz rundi)
const B_C:  usize = 2;   // b[k]
const C_C:  usize = 3;   // c[k]
const P_C:  usize = 4;   // P[k]=(k·B)[k]+carry     -- range-check tok
const PCIN: usize = 5;   // carry-in za P
const BP_C: usize = 6;   // |b'[k]| (izlaz)         -- range-check tok
const W_C:  usize = 7;   // W[k]=A'[k]-|b'[k]|      -- range-check tok
const WBIN: usize = 8;   // borrow-in za W
const WBOUT:usize = 9;   // borrow-out za W
const ISB:  usize = 10;  // is_block_boundary: 1 na poslednjem limb-redu rundi
const INBLK:usize = 11;  // in-block pozicija indikator: 1 ako je k < L (aktivni form-limb)
const T_C:  usize = 12;  // deljena tablica [0,N)
const M_P:  usize = 13;  // mult za P
const M_BP: usize = 14;  // mult za |b'|
const M_W:  usize = 15;  // mult za W
const CTR:  usize = 16;  // brojač punog stepena
const RIDX: usize = 17;  // indeks rundi (raste na granici bloka)
const TAGA: usize = 18;  // perm tag za a-limb = (r-1)*L + p   (committed)
const TAGC: usize = 19;  // perm tag za c-limb = r*L + p
const MAIN_W: usize = 20;

const NUM_LU: usize = 3; // P, |b'|, W dele JEDNU tablicu
const LU_VAL: [usize; NUM_LU] = [P_C, BP_C, W_C];
const LU_MUL: [usize; NUM_LU] = [M_P, M_BP, M_W];

// Aux segment: NUM_LU LogUp akumulatora + 1 grand-product Z (vezivanje lanca c(r)==a(r+1)).
// Sada je inter-blok vezivanje forme ENFORCED (permutacija nad (tag,val), tag=committed).
// Izazovi: alpha (LogUp), gamma (perm fold); beta = gamma² (grand-product baza).
const AUX_Z: usize = NUM_LU;
const AUX_W: usize = NUM_LU + 1;

// ============================ custom Trace ============================
struct MergeTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl MergeTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        MergeTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [AUX_W], [2]), length }
    }
}
impl Trace for MergeTrace {
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
        let gamma = rand[1];
        let beta = gamma * gamma;
        let n = self.length;
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
        let mut cols: Vec<Vec<E>> = (0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect();
        // grand-product Z za vezivanje lanca: Z[i]=proizvod doprinosa redova <i (Z[0]=1).
        // Doprinos form-reda (INBLK=1): (beta - e_a)/(beta - e_c), e = tag + gamma·val.
        let mut z = vec![E::ONE; n];
        let mut acc = E::ONE;
        for i in 0..n {
            z[i] = acc;
            if self.main.get(INBLK, i) == BaseElement::ONE {
                let av = E::from(self.main.get(A_C, i));
                let cv = E::from(self.main.get(C_C, i));
                let ta = E::from(self.main.get(TAGA, i));
                let tc = E::from(self.main.get(TAGC, i));
                let ea = ta + gamma*av;
                let ec = tc + gamma*cv;
                acc = acc * (beta - ea) * (beta - ec).inv();
            }
        }
        cols.push(z);
        Some(ColMatrix::new(cols))
    }
}

// ============================ public inputs ============================
#[derive(Clone)]
struct Pub {
    // row0 (vezuje trag) + LogUp row0 termovi + globalni |D| (kao skalar, disc-vezivanje)
    k0: BaseElement, a0: BaseElement, b0: BaseElement, c0: BaseElement,
    p0: BaseElement, bp0: BaseElement, w0: BaseElement,
    mp0: BaseElement, mbp0: BaseElement, mw0: BaseElement,
    dabs: BaseElement, n: usize,
    // finalna redukovana forma: prvih par limba izlaznog c poslednje rundi (javno svedočanstvo)
    c_fin0: BaseElement,
    // granični neupareni limbovi za grand-product zatvaranje:
    a_first: Vec<BaseElement>, // a-limbovi prvog bloka (r=0)
    c_last: Vec<BaseElement>,  // c-limbovi poslednjeg bloka (r=N_R-1)
}
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = vec![self.k0,self.a0,self.b0,self.c0,self.p0,self.bp0,self.w0,
             self.mp0,self.mbp0,self.mw0,self.dabs,BaseElement::new(self.n as u64),self.c_fin0];
        v.extend_from_slice(&self.a_first);
        v.extend_from_slice(&self.c_last);
        v
    }
}

struct MergeAir { context: AirContext<BaseElement>, p: Pub }
impl Air for MergeAir {
    type BaseField = BaseElement;
    type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let mut main_deg = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(1), // CTR advance
            TransitionConstraintDegree::new(2), // ISB bool
            TransitionConstraintDegree::new(2), // INBLK bool
            TransitionConstraintDegree::new(2), // P mult+carry
            TransitionConstraintDegree::new(1), // P carry link
            TransitionConstraintDegree::new(1), // W normalize
            TransitionConstraintDegree::new(1), // W borrow link
            TransitionConstraintDegree::new(2), // WBOUT bool
            TransitionConstraintDegree::new(2), // K broadcast unutar bloka
            TransitionConstraintDegree::new(1), // RIDX advance
        ];
        let _ = &mut main_deg;
        let mut aux_deg = vec![TransitionConstraintDegree::new(3); NUM_LU];
        aux_deg.push(TransitionConstraintDegree::new(3)); // Z grand-product (INBLK·Z'·e_c)
        let n_main_assert = 5 + 7 + 1;
        let n_aux_assert = 2 * NUM_LU + 2; // + Z[0]=1, Z[ACTIVE]=zatvaranje
        let context = AirContext::new_multi_segment(
            ti, main_deg, aux_deg, n_main_assert, n_aux_assert, options);
        MergeAir { context, p }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current();
        let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        let isb = cur[ISB];
        let ingate = one - isb; // 1 unutar bloka, 0 na granici bloka

        result[0] = nxt[T_C] - cur[T_C] - one;   // tablica
        result[1] = nxt[CTR] - cur[CTR] - one;   // CTR pun stepen
        result[2] = isb * (isb - one);           // ISB bool
        result[3] = cur[INBLK] * (cur[INBLK] - one); // INBLK bool

        // (4) P mult+carry UNUTAR bloka (gejt ingate; carry se nosi u PCIN'):
        //     K·B[k] + PCIN == P[k] + RADIX·pcout, pcout = PCIN' (sledeći limb-red)
        let pcout = nxt[PCIN];
        result[4] = ingate * (cur[KMUL]*cur[B_C] + cur[PCIN] - (cur[P_C] + radix*pcout));
        // (5) carry link: eksplicitno vezivanje (drži jedinstvenost limba P sa LogUp P<RADIX)
        result[5] = ingate * ((cur[KMUL]*cur[B_C] + cur[PCIN] - cur[P_C]) - radix*pcout);
        // (6) normalize W = A'-|b'| ; A' (novo a) = c stare runde -> koristimo C_C
        result[6] = ingate * (cur[BP_C] + cur[W_C] + cur[WBIN] - (cur[C_C] + radix*cur[WBOUT]));
        // (7) W borrow link
        result[7] = ingate * (nxt[WBIN] - cur[WBOUT]);
        // (8) WBOUT bool
        result[8] = cur[WBOUT]*(cur[WBOUT]-one);
        // (9) k konstantan unutar bloka (na granici se resetuje na k naredne rundi)
        result[9] = ingate * (nxt[KMUL] - cur[KMUL]);
        // (10) RIDX raste tačno na granici bloka
        result[10] = nxt[RIDX] - cur[RIDX] - isb;
        // NB: P<RADIX, |b'|<RADIX, W<RADIX se proveravaju LogUp-om (aux) protiv T=[0,RADIX).
        // NB: POZICIONO vezivanje a(r+1)[k]==c(r)[k] je preko fiksnih ASERTACIJA (stride RR),
        //     jer susedni-frame ne dohvata stride-RR redove.
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(RIDX, 0, BaseElement::ZERO),
            Assertion::single(WBIN, 0, BaseElement::ZERO),
            Assertion::single(PCIN, 0, BaseElement::ZERO),
            Assertion::single(KMUL, 0, self.p.k0),
            Assertion::single(A_C, 0, self.p.a0),
            Assertion::single(B_C, 0, self.p.b0),
            Assertion::single(C_C, 0, self.p.c0),
            Assertion::single(P_C, 0, self.p.p0),
            Assertion::single(BP_C, 0, self.p.bp0),
            Assertion::single(W_C, 0, self.p.w0),
        ];
        // Vezivanje lanca a(r+1)[k]==c(r)[k] je ENFORCED grand-product permutacijom (aux Z):
        // tag=(r*L+p) za c, ((r-1)*L+p) za a -> isti tag za lančane parove; multiset jednakost
        // (Schwartz–Zippel po γ) => limb-po-limb jednakost. Granični a_first/c_last su javni.
        // Finalni c-limb je javan (svedočanstvo o izlaznoj formi).
        v.push(Assertion::single(C_C, ACTIVE - RR, self.p.c_fin0));
        v
    }

    fn evaluate_aux_transition<F, E>(
        &self, main: &EvaluationFrame<F>, aux: &EvaluationFrame<E>,
        _p: &[F], rand: &AuxTraceRandElements<E>, result: &mut [E],
    ) where
        F: FieldElement<BaseField = BaseElement>,
        E: FieldElement<BaseField = BaseElement> + ExtensionOf<F>,
    {
        let alpha = rand.get_segment_elements(0)[0];
        let gamma = rand.get_segment_elements(0)[1];
        let beta = gamma * gamma;
        let mn = main.next();
        let t = E::from(mn[T_C]);
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]);
            let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j];
            let sp = aux.next()[j];
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
        // Z grand-product (doprinos TEKUĆEG reda; INBLK gejt):
        //   INBLK=1: Z'·(β - e_c) == Z·(β - e_a)     e = tag + γ·val
        //   INBLK=0: Z' == Z
        let mc = main.current();
        let frm = E::from(mc[INBLK]);
        let ea = E::from(mc[TAGA]) + gamma * E::from(mc[A_C]);
        let ec = E::from(mc[TAGC]) + gamma * E::from(mc[C_C]);
        let z = aux.current()[AUX_Z];
        let zp = aux.next()[AUX_Z];
        let active = zp*(beta - ec) - z*(beta - ea);
        let idle = zp - z;
        result[NUM_LU] = frm*active + (E::ONE - frm)*idle;
    }

    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let gamma = rand.get_segment_elements(0)[1];
        let beta = gamma * gamma;
        let term0 = |v0: BaseElement, m0: BaseElement| -> E {
            (alpha - E::from(v0)).inv() - E::from(m0) * alpha.inv()
        };
        let v0 = [self.p.p0, self.p.bp0, self.p.w0];
        let m0 = [self.p.mp0, self.p.mbp0, self.p.mw0];
        let mut v = Vec::new();
        for j in 0..NUM_LU {
            v.push(Assertion::single(j, 0, term0(v0[j], m0[j])));
            v.push(Assertion::single(j, self.p.n - 1, E::ZERO));
        }
        // grand-product zatvaranje: neupareni a_first (tag=(-1)*L+p) i c_last (tag=(N_R-1)*L+p)
        let mut num = E::ONE; let mut den = E::ONE;
        for p in 0..L {
            let taga = E::ZERO - E::from(BaseElement::new(L as u64)) + E::from(BaseElement::new(p as u64));
            let ea = taga + gamma * E::from(self.p.a_first[p]);
            let tagc = E::from(BaseElement::new(((N_R-1)*L + p) as u64));
            let ec = tagc + gamma * E::from(self.p.c_last[p]);
            num = num * (beta - ea);
            den = den * (beta - ec);
        }
        let zfin = num * den.inv();
        v.push(Assertion::single(AUX_Z, 0, E::ONE));
        v.push(Assertion::single(AUX_Z, ACTIVE, zfin));
        v
    }
}

// ============================ Prover ============================
struct P { options: ProofOptions, dabs: BaseElement, c_fin0: BaseElement, a_first: Vec<BaseElement>, c_last: Vec<BaseElement> }
impl Prover for P {
    type BaseField = BaseElement;
    type Air = MergeAir;
    type Trace = MergeTrace;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, t: &Self::Trace) -> Pub {
        let g = |c: usize, r: usize| t.main.get(c, r);
        Pub {
            k0:g(KMUL,0), a0:g(A_C,0), b0:g(B_C,0), c0:g(C_C,0),
            p0:g(P_C,0), bp0:g(BP_C,0), w0:g(W_C,0),
            mp0:g(M_P,0), mbp0:g(M_BP,0), mw0:g(M_W,0),
            dabs: self.dabs, n: t.length(), c_fin0: self.c_fin0,
            a_first: self.a_first.clone(), c_last: self.c_last.clone(),
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
// Generiše N_R rundi; svaka runda = RR limb-redova pune narrow-long aritmetike.
// Za spajanje uzimamo koherentne male forme; ključno je da:
//  - P = k·B carry-lanac zatvara unutar svakog bloka,
//  - |b'| <= A' (=c) tako da W>=0 borrow-lanac zatvara,
//  - a(r+1)[k] = c(r)[k]  (rho a'=c) -> ulančavanje na limb-nivou.
struct Blk { k: u64, a: Vec<u64>, b: Vec<u64>, c: Vec<u64>, p: Vec<u64>, pcin: Vec<u64>,
             bp: Vec<u64>, w: Vec<u64>, wbin: Vec<u64>, wbout: Vec<u64> }

fn gen_block(k: u64, a: &[u64], b: &[u64], c: &[u64]) -> Blk {
    // P = k·B (RR limba, carry)
    let mut p = vec![0u64; RR]; let mut pcin = vec![0u64; RR];
    let mut carry = 0u64;
    for j in 0..RR {
        pcin[j] = carry;
        let bj = if j < L { b[j] } else { 0 };
        let acc = k*bj + carry; p[j] = acc % RADIX; carry = acc / RADIX;
    }
    // |b'| <= A'(=c): uzmemo bp = c sa nulom na najvišem limbu -> W>=0 lanac zatvara
    let aprime: Vec<u64> = (0..RR).map(|j| if j < L { c[j] } else { 0 }).collect();
    let bp: Vec<u64> = (0..RR).map(|j| if j < L-1 { aprime[j] } else { 0 }).collect();
    let mut w = vec![0u64; RR]; let mut wbin = vec![0u64; RR]; let mut wbout = vec![0u64; RR];
    let mut bin = 0i64;
    for j in 0..RR {
        wbin[j] = bin as u64;
        let lhs = aprime[j] as i64 - bp[j] as i64 - bin;
        let (wj, bout) = if lhs < 0 { ((lhs + RADIX as i64) as u64, 1i64) } else { (lhs as u64, 0i64) };
        w[j] = wj; wbout[j] = bout as u64; bin = bout;
    }
    Blk { k, a: a.to_vec(), b: b.to_vec(), c: c.to_vec(), p, pcin, bp, w, wbin, wbout }
}

fn gen_chain() -> (Vec<Blk>, u64) {
    // startni limbovi (mali, deterministicki)
    let mut rng = 0x1234_5678u64;
    let mut nx = || { rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; rng % RADIX };
    let mut a: Vec<u64> = (0..L).map(|_| nx()).collect();
    let mut b: Vec<u64> = (0..L).map(|_| nx()).collect();
    let mut c: Vec<u64> = (0..L).map(|_| nx()).collect();
    let dabs = 10803839u64; // simbolički |D| (disc-vezivanje kao javni ulaz; konstantno kroz blokove)
    let mut blocks = Vec::new();
    for _r in 0..N_R {
        let k = 3; // mali koef (par bita), kao izmereno (|k| ~ 13-bit worst case)
        let blk = gen_block(k, &a, &b, &c);
        // ULANČAVANJE (rho a'=c, b'=..., c'=...): naredna runda dobija a=c, a novo b,c
        // koherentno malo. Za integraciju: a_next = c (limb-po-limb), b_next = b' magnitude, c_next = a.
        let a_next = c.clone();
        let b_next = blk.bp.iter().take(L).cloned().collect::<Vec<_>>();
        let c_next = a.clone();
        blocks.push(blk);
        a = a_next; b = b_next; c = c_next;
    }
    (blocks, dabs)
}

#[derive(Clone, Copy)]
enum Tamper { None, MulLimb(usize), WLimb(usize), OutOfRange(usize, u64), ChainBreak(usize) }

fn build_trace(blocks: &[Blk], dabs: u64, tamper: Tamper) -> (MergeTrace, Pub) {
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i] = BaseElement::new(i as u64); col[CTR][i] = BaseElement::new(i as u64); }
    for (r, blk) in blocks.iter().enumerate() {
        let base = r * RR;
        for j in 0..RR {
            let i = base + j;
            col[KMUL][i] = BaseElement::new(blk.k);
            col[A_C][i]  = BaseElement::new(if j < L { blk.a[j] } else { 0 });
            col[B_C][i]  = BaseElement::new(if j < L { blk.b[j] } else { 0 });
            col[C_C][i]  = BaseElement::new(if j < L { blk.c[j] } else { 0 });
            col[P_C][i]  = BaseElement::new(blk.p[j]);
            col[PCIN][i] = BaseElement::new(blk.pcin[j]);
            col[BP_C][i] = BaseElement::new(blk.bp[j]);
            col[W_C][i]  = BaseElement::new(blk.w[j]);
            col[WBIN][i] = BaseElement::new(blk.wbin[j]);
            col[WBOUT][i]= BaseElement::new(blk.wbout[j]);
            col[INBLK][i]= BaseElement::new(if j < L { 1 } else { 0 });
            col[ISB][i]  = BaseElement::new(if j == RR-1 { 1 } else { 0 });
            col[RIDX][i] = BaseElement::new(r as u64);
            if j < L {
                let p = j;
                col[TAGC][i] = BaseElement::new((r*L + p) as u64);
                col[TAGA][i] = if r == 0 {
                    BaseElement::ZERO - BaseElement::new(L as u64) + BaseElement::new(p as u64)
                } else {
                    BaseElement::new(((r-1)*L + p) as u64)
                };
            }
        }
    }
    // Granica poslednjeg aktivnog bloka -> prvi padding red mora zadovoljiti ISB constraint:
    // ISB[ACTIVE-1]=1 -> RIDX'[ACTIVE] = RIDX+1 = N_R. K broadcast gejtan ISB (na granici slobodno).
    // Padding: sve 0 osim RIDX (konstantan), k=0. P=0,B=0 -> P mult trivijalno; W=0 -> normalize 0.
    for i in ACTIVE..N {
        col[RIDX][i] = BaseElement::new(N_R as u64);
        // ISB=0, INBLK=0, sve vrednosti 0 -> transicije: P mult (ingate=1): 0+0==0+0 OK;
        // W normalize (ingate=1): 0+0+WBIN==0+0 -> treba WBIN chain 0. WBIN=0 svuda u padding-u OK.
        // carry link 0 OK. K broadcast (ingate=1): 0-0 OK.
    }
    // Prvi padding red posle poslednjeg bloka: poslednji aktivni red ima ISB=1 (kraj bloka),
    // pa je P/W gejt ingate=0 tamo -> nema uslova ka padding-u osim RIDX i CTR/T (ispunjeni).

    // tamper (negativni testovi)
    match tamper {
        Tamper::None => {}
        Tamper::MulLimb(r) => {
            // in-range promena P u bloku r -> mult+carry puca (LogUp ostaje balansiran preko mult)
            let i = r*RR + 5;
            let v = (col[P_C][i].as_int() + 1) % RADIX;
            col[P_C][i] = BaseElement::new(v);
        }
        Tamper::WLimb(r) => {
            let i = r*RR + 5;
            let v = (col[W_C][i].as_int() + 1) % RADIX;
            col[W_C][i] = BaseElement::new(v);
        }
        Tamper::OutOfRange(r, val) => {
            let i = r*RR + 5;
            col[P_C][i] = BaseElement::new(val); // van [0,2^16) -> LogUp
        }
        Tamper::ChainBreak(r) => {
            // pokvari a-limb u bloku r (INBLK red) -> grand-product ne balansira -> perm hvata
            let i = r*RR + 2;
            col[A_C][i] = col[A_C][i] + BaseElement::ONE;
        }
    }

    // multipliciteti za LogUp tokove
    for j in 0..NUM_LU {
        let (vcol, mcol) = (LU_VAL[j], LU_MUL[j]);
        let mut mult = vec![0u64; N];
        for i in 0..N { let v = col[vcol][i].as_int(); if (v as usize) < N { mult[v as usize] += 1; } }
        for i in 0..N { col[mcol][i] = BaseElement::new(mult[i]); }
    }

    let g = |c: &Vec<Vec<BaseElement>>, cc: usize, r: usize| c[cc][r];
    let p = Pub {
        k0:g(&col,KMUL,0), a0:g(&col,A_C,0), b0:g(&col,B_C,0), c0:g(&col,C_C,0),
        p0:g(&col,P_C,0), bp0:g(&col,BP_C,0), w0:g(&col,W_C,0),
        mp0:g(&col,M_P,0), mbp0:g(&col,M_BP,0), mw0:g(&col,M_W,0),
        dabs: BaseElement::new(dabs), n: N,
        c_fin0: g(&col, C_C, ACTIVE - RR), // prvi c-limb poslednje rundi
        a_first: (0..L).map(|p| col[A_C][p]).collect(),          // a-limbovi bloka 0
        c_last:  (0..L).map(|p| col[C_C][(N_R-1)*RR + p]).collect(), // c-limbovi poslednjeg bloka
    };
    (MergeTrace::new(col), p)
}

fn run(blocks: &[Blk], dabs: u64, tamper: Tamper, label: &str, expect_ok: bool) {
    let (trace, pi) = build_trace(blocks, dabs, tamper);
    let options = ProofOptions::new(36, 8, 16, FieldExtension::Quadratic, 4, 31);
    let prover = P { options, dabs: pi.dabs, c_fin0: pi.c_fin0, a_first: pi.a_first.clone(), c_last: pi.c_last.clone() };
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t0 = Instant::now();
        let proof = prover.prove(trace).expect("prove");
        let pm = t0.elapsed().as_secs_f64()*1000.0;
        let pb = proof.to_bytes().len();
        let sec = proof.security_level::<H>(true);
        let mo = winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let t1 = Instant::now();
        let ok = winterfell::verify::<MergeAir, H, RC>(proof, pi.clone(), &mo).is_ok();
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
    println!("== KORAK 3: SPAJANJE — svaka runda = 64-limb BLOK ({} reda), {} rundi ulančano ==", RR, N_R);
    println!("glavne kolone: {} + aux (LogUp): {} = {} (< 255)", MAIN_W, NUM_LU, MAIN_W+NUM_LU);
    println!("aktivnih redova: {} (= {} rundi × {} limb-reda) ; N = {} (tablica dominira)",
             ACTIVE, N_R, RR, N);
    println!("mehanizmi u JEDNOM tragu: 64-limb mult+carry (P=k·B) + normalize (W>=0)");
    println!("  + LogUp range-check + PERM vezivanje lanca (grand-product) + CTR ; |D| javni ulaz\n");

    let (blocks, dabs) = gen_chain();
    // sanity: sve range-check vrednosti < 2^16
    for blk in &blocks {
        assert!(blk.p.iter().all(|&x| x<RADIX), "P van opsega");
        assert!(blk.bp.iter().all(|&x| x<RADIX), "bp van opsega");
        assert!(blk.w.iter().all(|&x| x<RADIX), "w van opsega");
    }
    println!("startni blok: k={} ; a[0]={} b[0]={} c[0]={} ; |D|={} (disc-vezivanje)",
             blocks[0].k, blocks[0].a[0], blocks[0].b[0], blocks[0].c[0], dabs);

    run(&blocks, dabs, Tamper::None, "[validan]   228 blokova × 64-limb ulančano", true);
    run(&blocks, dabs, Tamper::OutOfRange(30, 70000), "[negativan] P van [0,2^16) @blok 30 (LogUp)", false);
    run(&blocks, dabs, Tamper::MulLimb(50), "[negativan] P pogrešan proizvod @blok 50 (mult+carry)", false);
    run(&blocks, dabs, Tamper::WLimb(100), "[negativan] W pogrešan @blok 100 (normalize)", false);
    run(&blocks, dabs, Tamper::ChainBreak(60), "[negativan] a-limb @blok 60 (prekinut lanac, PERM)", false);

    println!("\nSVE PROSLO: Korak 1 (64-limb blok-aritmetika) + Korak 2 (ulančavanje) spojeni u");
    println!("JEDAN trag pod JEDNOM deljenom LogUp tablicom; {} kolona ≪ 255.", MAIN_W+NUM_LU);
}
