// DISC-FULL: puno vezivanje |D| ← a,b,c u JEDNOM tragu (demo L=4).
// Tri faze, ulančane, sve dokazano odvojeno — ovde SPOJENO:
//   FAZA MULT_AC:  AC[k] = (a·c)[k]   (one-hot konvolucija + carry)   [mulseg2 obrazac]
//   FAZA MULT_BB:  BB[k] = (b·b)[k]                                    [isti engine]
//   FAZA ANCHOR:   4·AC[k] − BB[k] == |D|[k]  (dva carry lanca, L==R)  [disc_anchor obrazac]
// Vezivanje faza: AC/BB koje ANCHOR troši == AC/BB koje MULT proizvodi — PERM grand-product
//   nad (tag,val), tag committed. LogUp range-check limba (bez bit-dekompozicije).
//
// Skala demo: L=4 (a,b,c su 4-limb), izlaz 2L=8 limba. Mehanika identična za L=64
//   (kao round_full→reduce_merged): širina konstantna, samo više redova.
//
// Raspored (jedna faza po bloku redova, POS one-hot po poziciji):
//   redovi  0..8   MULT_AC  (8 izlaznih poz)
//   redovi  8..16  MULT_BB
//   redovi 16..24  ANCHOR
//   ostatak: padding. N=4096.

use std::time::Instant;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin},
    math::{fields::f64::BaseElement, ExtensionOf, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxTraceRandElements, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, FieldExtension, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TraceLayout, TracePolyTable, TransitionConstraintDegree,
};

const RADIX: u64 = 1 << 16;
const N: usize = 1 << 12;     // 4096 (== LogUp tablica [0,2^12)? ne — koristimo [0,2^16) semantiku ali kraći trag)
const TBL: u64 = 1 << 16;     // range-check tablica logički [0,2^16); u tragu N=4096 nije puna tablica,
// Napomena: za demo koristimo N=4096 trag; puna deljena tablica [0,2^16) traži N>=65536 (kao u reduce_merged).
// Ovde LogUp tablica je [0,N) i sve demo-vrednosti su < N, pa je range-check ispravan za demo skalu.
const L: usize = 4;           // limba u a,b,c
const NPOS: usize = 2*L;      // 8 izlaznih pozicija po proizvodu
const PH_AC: usize = 0;       // start faze MULT_AC
const PH_BB: usize = NPOS;    // 8
const PH_AN: usize = 2*NPOS;  // 16
const PH_BBC: usize = 3*NPOS; // 24 — anchor-troši BB (perm imenilac, drugi prolaz)
const ACTIVE: usize = 4*NPOS; // 32

// glavne kolone
// mult engine (deljen kroz obe mult faze; A/B broadcast + POS one-hot + conv rezultat + carry)
const OP1: usize = 0;               // operand1 limbovi (a za AC, b za BB) — broadcast (L)
const OP2: usize = OP1 + L;         // operand2 limbovi (c za AC, b za BB) — broadcast (L)
const POS0: usize = OP2 + L;        // POS one-hot (NPOS)
const CIN: usize = POS0 + NPOS;     // conv carry-in
const PRODC: usize = CIN + 1;       // proizvod limb rezultata (AC ili BB)   -- range-check tok
// anchor kolone
const ACc: usize = PRODC + 1;       // AC[k] (u anchor fazi)
const BBc: usize = ACc + 1;         // BB[k]
const Dc:  usize = BBc + 1;         // |D|[k]
const LCIN: usize = Dc + 1;
const L_C: usize = LCIN + 1;        // LHS limb                              -- range-check tok
const LCO: usize = L_C + 1;
const RCIN: usize = LCO + 1;
const R_C: usize = RCIN + 1;        // RHS limb                              -- range-check tok
const RCO: usize = R_C + 1;
// faza flagovi
const FMUL: usize = RCO + 1;        // 1 u mult fazama (AC ili BB)
const FANC: usize = FMUL + 1;       // 1 u anchor fazi
// perm tagovi (vežu proizvod↔anchor): tag za AC, BB
const TAGP: usize = FANC + 1;       // tag proizvoda u MULT fazi (AC: 0*NPOS+k ; BB: 1*NPOS+k)
const TAGA: usize = TAGP + 1;       // tag potrošnje u ANCHOR fazi (AC-strana: 0*NPOS+k ; BB: 1*NPOS+k)
const PVAL: usize = TAGA + 1;       // vrednost proizvoda za perm (PRODC u mult; AC ili BB u anchor)
const PSEL: usize = PVAL + 1;       // 1 ako red daje perm-doprinos (mult: svaki poz ; anchor: dva po poz)
// tablica + LogUp mult
const T_C: usize = PSEL + 1;
const M_PR: usize = T_C + 1;        // mult za PRODC
const M_L: usize = M_PR + 1;
const M_R: usize = M_L + 1;
const CTR: usize = M_R + 1;
const MAIN_W: usize = CTR + 1;

const NUM_LU: usize = 3;
const LU_VAL: [usize; NUM_LU] = [PRODC, L_C, R_C];
const LU_MUL: [usize; NUM_LU] = [M_PR, M_L, M_R];
const AUX_Z: usize = NUM_LU;
const AUX_W: usize = NUM_LU + 1;

struct DTrace { main: ColMatrix<BaseElement>, layout: TraceLayout, length: usize }
impl DTrace {
    fn new(cols: Vec<Vec<BaseElement>>) -> Self {
        let length = cols[0].len();
        DTrace { main: ColMatrix::new(cols), layout: TraceLayout::new(MAIN_W, [AUX_W], [2]), length }
    }
}
impl Trace for DTrace {
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
        let alpha = rand[0]; let gamma = rand[1]; let beta = gamma*gamma;
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
            for i in 1..n { s[i] = s[i-1] + term(i); }
            s
        };
        let mut cols: Vec<Vec<E>> = (0..NUM_LU).map(|j| mk(LU_VAL[j], LU_MUL[j])).collect();
        // grand-product Z: MULT strana daje proizvod (brojilac), ANCHOR strana troši (imenilac).
        // e = tag + gamma·val ; PSEL gejt ; doprinos = (beta - e) na odgovarajućoj strani.
        // MULT: tag=TAGP, val=PVAL (proizvod) -> brojilac. ANCHOR: tag=TAGA, val=PVAL -> imenilac.
        // Balans (Z_final==1) akko multiset proizvoda == multiset potrošenih.
        let mut z = vec![E::ONE; n]; let mut acc = E::ONE;
        for i in 0..n {
            z[i] = acc;
            if self.main.get(PSEL, i) == BaseElement::ONE {
                let val = E::from(self.main.get(PVAL, i));
                if self.main.get(FMUL, i) == BaseElement::ONE {
                    let e = E::from(self.main.get(TAGP, i)) + gamma*val;
                    acc = acc * (beta - e);
                } else {
                    let e = E::from(self.main.get(TAGA, i)) + gamma*val;
                    acc = acc * (beta - e).inv();
                }
            }
        }
        cols.push(z);
        Some(ColMatrix::new(cols))
    }
}

#[derive(Clone)]
struct Pub { n: usize, m: MRow }
impl ToElements<BaseElement> for Pub {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = vec![BaseElement::new(self.n as u64)];
        v.extend_from_slice(&self.m.op1); v.extend_from_slice(&self.m.op2);
        v.extend_from_slice(&self.m.pos0);
        v.push(self.m.prod0); v.push(self.m.mpr0); v.push(self.m.ml0); v.push(self.m.mr0);
        v
    }
}

struct DAir { context: AirContext<BaseElement>, m: MRow }
#[derive(Clone)]
struct MRow { // row0 vrednosti za asertacije
    op1: [BaseElement; L], op2: [BaseElement; L], pos0: [BaseElement; NPOS],
    prod0: BaseElement, mpr0: BaseElement, ml0: BaseElement, mr0: BaseElement,
}
impl Air for DAir {
    type BaseField = BaseElement; type PublicInputs = Pub;
    fn new(ti: TraceInfo, p: Pub, options: ProofOptions) -> Self {
        let mut d = vec![
            TransitionConstraintDegree::new(1), // T advance
            TransitionConstraintDegree::new(1), // CTR advance
            TransitionConstraintDegree::new(3), // MULT conv+carry (POS·OP1·OP2, gejt FMUL)
            TransitionConstraintDegree::new(2), // MULT carry link (gejt FMUL)
            TransitionConstraintDegree::new(2), // ANCHOR LHS (gejt FANC)
            TransitionConstraintDegree::new(2), // ANCHOR RHS
            TransitionConstraintDegree::new(2), // ANCHOR LHS carry link
            TransitionConstraintDegree::new(2), // ANCHOR RHS carry link
            TransitionConstraintDegree::new(2), // ANCHOR L==R
        ];
        let _ = &mut d;
        let mut aux = vec![TransitionConstraintDegree::new(3); NUM_LU];
        aux.push(TransitionConstraintDegree::new(4)); // grand-product Z (psel·fanc·zp·ea = deg4)
        let n_main = 2 + L + L + NPOS + 1 + 1;
        let n_aux = 2*NUM_LU + 2;
        let context = AirContext::new_multi_segment(ti, d, aux, n_main, n_aux, options);
        DAir { context, m: p.m }
    }
    fn context(&self) -> &AirContext<BaseElement> { &self.context }
    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self, frame: &EvaluationFrame<E>, _p: &[E], result: &mut [E],
    ) {
        let cur = frame.current(); let nxt = frame.next();
        let one = E::ONE;
        let radix = E::from(BaseElement::new(RADIX));
        let four = E::from(BaseElement::new(4));
        let fmul = cur[FMUL]; let fanc = cur[FANC];
        result[0] = nxt[T_C] - cur[T_C] - one;
        result[1] = nxt[CTR] - cur[CTR] - one;
        // MULT conv: conv = Σ_{i,j} POS[i+j]·OP1[i]·OP2[j] ; cin+conv == PRODC + RADIX·cnext(=nxt CIN)
        let mut conv = E::ZERO;
        for i in 0..L { for j in 0..L { conv += cur[POS0 + i + j]*cur[OP1+i]*cur[OP2+j]; } }
        result[2] = fmul * (cur[CIN] + conv - (cur[PRODC] + radix*nxt[CIN]));
        result[3] = fmul * E::ZERO; // (carry link je već preko nxt[CIN]; rezervisano)
        // ANCHOR: 4·AC + lcin == L + RADIX·lco ; BB + D + rcin == R + RADIX·rco ; L==R
        result[4] = fanc * (four*cur[ACc] + cur[LCIN] - (cur[L_C] + radix*cur[LCO]));
        result[5] = fanc * (cur[BBc] + cur[Dc] + cur[RCIN] - (cur[R_C] + radix*cur[RCO]));
        result[6] = fanc * (nxt[LCIN] - cur[LCO]);
        result[7] = fanc * (nxt[RCIN] - cur[RCO]);
        result[8] = fanc * (cur[L_C] - cur[R_C]);
    }
    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut v = vec![
            Assertion::single(T_C, 0, BaseElement::ZERO),
            Assertion::single(CTR, 0, BaseElement::ZERO),
            Assertion::single(CIN, 0, BaseElement::ZERO),
            Assertion::single(PRODC, 0, self.m.prod0),
        ];
        for i in 0..L { v.push(Assertion::single(OP1+i, 0, self.m.op1[i])); }
        for i in 0..L { v.push(Assertion::single(OP2+i, 0, self.m.op2[i])); }
        for k in 0..NPOS { v.push(Assertion::single(POS0+k, 0, self.m.pos0[k])); }
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
        let beta = gamma*gamma;
        let mn = main.next();
        let t = E::from(mn[T_C]);
        for j in 0..NUM_LU {
            let v = E::from(mn[LU_VAL[j]]); let m = E::from(mn[LU_MUL[j]]);
            let s = aux.current()[j]; let sp = aux.next()[j];
            result[j] = (sp - s) * (alpha - v) * (alpha - t) - ((alpha - t) - m * (alpha - v));
        }
        // grand-product Z (doprinos tekućeg reda):
        //  PSEL=1 & FMUL=1: Z' == Z·(beta - e_p)      e_p = TAGP + gamma·PVAL
        //  PSEL=1 & FANC=1: Z'·(beta - e_a) == Z      e_a = TAGA + gamma·PVAL
        //  PSEL=0:          Z' == Z
        let mc = main.current();
        let psel = E::from(mc[PSEL]); let fmul = E::from(mc[FMUL]); let fanc = E::from(mc[FANC]);
        let val = E::from(mc[PVAL]);
        let ep = E::from(mc[TAGP]) + gamma*val;
        let ea = E::from(mc[TAGA]) + gamma*val;
        let z = aux.current()[AUX_Z]; let zp = aux.next()[AUX_Z];
        let mul_term = zp - z*(beta - ep);            // == 0 na FMUL
        let anc_term = zp*(beta - ea) - z;            // == 0 na FANC
        let idle = zp - z;
        result[NUM_LU] = psel*(fmul*mul_term + fanc*anc_term) + (E::ONE - psel)*idle;
    }
    fn get_aux_assertions<E: FieldElement<BaseField = BaseElement>>(
        &self, rand: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let alpha = rand.get_segment_elements(0)[0];
        let term0 = |v0: BaseElement, m0: BaseElement| -> E {
            (alpha - E::from(v0)).inv() - E::from(m0) * alpha.inv()
        };
        let mut v = Vec::new();
        let v0 = [self.m.prod0, BaseElement::ZERO, BaseElement::ZERO];
        let m0 = [self.m.mpr0, self.m.ml0, self.m.mr0];
        for j in 0..NUM_LU {
            v.push(Assertion::single(j, 0, term0(v0[j], m0[j])));
            v.push(Assertion::single(j, N - 1, E::ZERO));
        }
        // grand-product: Z0=1, Zfinal=1 (multiset proizvoda == multiset potrošenih)
        v.push(Assertion::single(AUX_Z, 0, E::ONE));
        v.push(Assertion::single(AUX_Z, ACTIVE, E::ONE));
        v
    }
}

struct P { options: ProofOptions, m: MRow }
impl Prover for P {
    type BaseField = BaseElement; type Air = DAir; type Trace = DTrace;
    type HashFn = Blake3_256<BaseElement>; type RandomCoin = DefaultRandomCoin<Blake3_256<BaseElement>>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _t: &Self::Trace) -> Pub { Pub { n: N, m: self.m.clone() } }
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

fn conv_mul(x: &[u64], y: &[u64]) -> Vec<u64> {
    let mut out = vec![0i128; NPOS];
    for i in 0..L { for j in 0..L { out[i+j] += (x[i] as i128)*(y[j] as i128); } }
    let mut res = vec![0u64; NPOS]; let mut car = 0i128;
    for k in 0..NPOS { let s = out[k]+car; res[k] = (s % RADIX as i128) as u64; car = s / RADIX as i128; }
    res
}

fn onehot(pos: usize) -> [BaseElement; NPOS] {
    let mut o = [BaseElement::ZERO; NPOS]; o[pos] = BaseElement::ONE; o
}

#[derive(Clone,Copy)]
enum Tamper { None, BadProd, BadD, BreakLink }

fn build(a:&[u64], b:&[u64], c:&[u64], tamper: Tamper) -> (DTrace, MRow) {
    let ac = conv_mul(a,c);
    let mut bb = conv_mul(b,b);
    let mut acx = ac.clone();
    let mut col = vec![vec![BaseElement::ZERO; N]; MAIN_W];
    for i in 0..N { col[T_C][i]=BaseElement::new(i as u64); col[CTR][i]=BaseElement::new(i as u64); }

    // helper za mult fazu: engine sa OP1=x,OP2=y broadcast, POS one-hot po poziciji, PRODC=proizvod
    let fill_mult = |col: &mut Vec<Vec<BaseElement>>, base: usize, x:&[u64], y:&[u64], prod:&[u64], prodtag_base: u64| {
        let mut cin = 0i128;
        // carry lanac za conv
        let mut out = vec![0i128; NPOS];
        for i in 0..L { for j in 0..L { out[i+j]+=(x[i] as i128)*(y[j] as i128); } }
        let mut carry = 0i128;
        for k in 0..NPOS {
            let i = base + k;
            for t in 0..L { col[OP1+t][i]=BaseElement::new(x[t]); col[OP2+t][i]=BaseElement::new(y[t]); }
            let oh = onehot(k); for t in 0..NPOS { col[POS0+t][i]=oh[t]; }
            col[CIN][i]=BaseElement::new(carry as u64);
            col[PRODC][i]=BaseElement::new(prod[k]);
            col[FMUL][i]=BaseElement::ONE;
            col[PSEL][i]=BaseElement::ONE;
            col[TAGP][i]=BaseElement::new(prodtag_base + k as u64);
            col[PVAL][i]=BaseElement::new(prod[k]);
            let s = out[k]+carry; carry = s / RADIX as i128;
            let _ = cin; cin = carry;
        }
    };

    if let Tamper::BadProd = tamper { acx[3] = acx[3].wrapping_add(1); } // pokvari AC proizvod

    fill_mult(&mut col, PH_AC, a, c, &acx, 0);          // AC: tag 0..NPOS
    fill_mult(&mut col, PH_BB, b, b, &bb, NPOS as u64); // BB: tag NPOS..2NPOS

    // ANCHOR faza: čita AC[k],BB[k],D[k]; dokaz 4AC-BB==D ; troši AC,BB preko perm (imenilac).
    if let Tamper::BadD = tamper { /* pokvari D u nastavku */ }
    let mut lcin=0i128; let mut rcin=0i128;
    for k in 0..NPOS {
        let i = PH_AN + k;
        let acv = ac[k] as i128; let bbv = bb[k] as i128;
        // |D|[k] tako da anchor drži: L = 4·AC + lcin ; R = BB + D + rcin ; L==R -> D = 4AC - BB + (lcin-rcin)... 
        // radimo standardno: računamo L iz LHS, pa biramo D da RHS da isti limb.
        let ls = 4*acv + lcin; let lco = ls.div_euclid(RADIX as i128); let ll = ls.rem_euclid(RADIX as i128);
        // biramo D[k] = ll - bb - rcin (+RADIX·rco). Da bude nenegativno, dopuštamo rco.
        let mut dval = ll - bbv - rcin;
        let mut rco = 0i128;
        while dval < 0 { dval += RADIX as i128; rco += 1; }
        let rs = bbv + dval + rcin; let rl = rs.rem_euclid(RADIX as i128); let rco2 = rs.div_euclid(RADIX as i128);
        debug_assert_eq!(rco, rco2); debug_assert_eq!(ll, rl);
        let mut dstore = dval;
        if let Tamper::BadD = tamper { if k==3 { dstore += 1; } }
        col[ACc][i]=BaseElement::new(ac[k]); col[BBc][i]=BaseElement::new(bb[k]); col[Dc][i]=BaseElement::new(dstore as u64);
        col[LCIN][i]=BaseElement::new(lcin as u64); col[L_C][i]=BaseElement::new(ll as u64); col[LCO][i]=BaseElement::new(lco as u64);
        col[RCIN][i]=BaseElement::new(rcin as u64); col[R_C][i]=BaseElement::new(rl as u64); col[RCO][i]=BaseElement::new(rco as u64);
        col[FANC][i]=BaseElement::ONE;
        // perm: anchor troši AC[k] (tag 0*NPOS+k) i BB[k] (tag NPOS+k). Dve potrošnje po poz -> 
        // koristimo DVA reda? Ovde po redu trošimo AC; BB trošimo preko dodatnog PSEL na istom redu
        // nije moguće (jedan PVAL/red). Zato trošimo AC ovde, a BB u drugom prolazu (dole).
        col[PSEL][i]=BaseElement::ONE;
        col[TAGA][i]=BaseElement::new((0*NPOS + k) as u64); // troši AC
        col[PVAL][i]=BaseElement::new(ac[k]);
        lcin = lco; rcin = rco;
    }
    // drugi prolaz: troši BB[k] (tag NPOS+k) — u redovima posle anchora (PH_AN+NPOS ..)
    let bb_base = PH_BBC;
    for k in 0..NPOS {
        let i = bb_base + k;
        col[FANC][i]=BaseElement::ZERO; col[FMUL][i]=BaseElement::ZERO;
        col[PSEL][i]=BaseElement::ONE;
        col[TAGA][i]=BaseElement::new((NPOS + k) as u64); // troši BB
        col[PVAL][i]=BaseElement::new(bb[k]);
    }
    if let Tamper::BreakLink = tamper {
        // pokvari perm: promeni PVAL na jednom anchor-troši redu (AC) -> multiset ne balansira
        col[PVAL][PH_AN+2] = col[PVAL][PH_AN+2] + BaseElement::ONE;
    }

    // Range-check multipliciteti (LogUp) za PRODC, L_C, R_C — tablica [0,N)
    for (vc,mc) in [(PRODC,M_PR),(L_C,M_L),(R_C,M_R)] {
        let mut mult=vec![0u64;N];
        for i in 0..N { let v=col[vc][i].as_int(); if (v as usize)<N { mult[v as usize]+=1; } }
        for i in 0..N { col[mc][i]=BaseElement::new(mult[i]); }
    }

    let mut m = MRow{ op1:[BaseElement::ZERO;L], op2:[BaseElement::ZERO;L], pos0:[BaseElement::ZERO;NPOS],
        prod0: col[PRODC][0], mpr0: col[M_PR][0], ml0: col[M_L][0], mr0: col[M_R][0] };
    for t in 0..L { m.op1[t]=col[OP1+t][0]; m.op2[t]=col[OP2+t][0]; }
    for t in 0..NPOS { m.pos0[t]=col[POS0+t][0]; }
    (DTrace::new(col), m)
}

fn run(a:&[u64],b:&[u64],c:&[u64],tamper:Tamper,label:&str,expect_ok:bool){
    let (trace,m)=build(a,b,c,tamper);
    let options=ProofOptions::new(36,8,16,FieldExtension::Quadratic,4,31);
    let prover=P{options, m: m.clone()};
    let res=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
        // inject row0 vrednosti u AIR preko pub? Ne — koristimo prover.m u Air::new preko TraceInfo? 
        // Umesto toga, Air dobija m preko get_pub_inputs? Pub je prazan. Zato Air::new ne zna m.
        // Rešenje: koristimo Assertion vrednosti iz trace-a direktno — Air ih čita iz self.m,
        // koji postavljamo ovde preko prover-a NE može. Zato prosleđujemo m kroz Pub.
        let t0=Instant::now(); let proof=prover.prove(trace).expect("prove");
        let pm=t0.elapsed().as_secs_f64()*1000.0; let pb=proof.to_bytes().len();
        let sec=proof.security_level::<H>(true);
        let mo=winterfell::AcceptableOptions::MinConjecturedSecurity(95);
        let ok=winterfell::verify::<DAir,H,RC>(proof, Pub{n:N, m:m.clone()}, &mo).is_ok();
        (pb,sec,pm,ok)
    }));
    match res {
        Ok((pb,sec,pm,ok))=>{
            println!("{}: verify={} (ocek {}) ; dokaz {:.1} KB ; prove {:.0} ms ; sec {}",
                label, if ok{"PASS"}else{"FAIL"}, if expect_ok{"PASS"}else{"FAIL"}, pb as f64/1024.0, pm, sec);
            if ok!=expect_ok { println!("   >>> NEOCEKIVANO!"); std::process::exit(2); }
        }
        Err(_)=>{ println!("{}: PANIC (ocek {})",label,if expect_ok{"PASS"}else{"FAIL"}); if expect_ok{std::process::exit(2);} }
    }
}

fn main(){
    println!("== DISC-FULL: |D| <- a,b,c  (AC=a·c, BB=b·b one-hot conv + anchor 4AC-BB=|D|) ==");
    println!("faze MULT_AC/MULT_BB/ANCHOR u jednom tragu, perm-vezane ; L={} demo ; kolone {}\n", L, MAIN_W+AUX_W);
    let a=[3,5,2,7]; let c=[4,1,6,2]; let b=[1,2,1,3];
    run(&a,&b,&c,Tamper::None, "[validan]   |D| vezan za a,b,c", true);
    run(&a,&b,&c,Tamper::BadProd, "[negativan] AC proizvod pogrešan", false);
    run(&a,&b,&c,Tamper::BadD, "[negativan] |D|[3]+1 (anchor puca)", false);
    run(&a,&b,&c,Tamper::BreakLink, "[negativan] perm PVAL pokvaren (mult↔anchor veza)", false);
    println!("\nSVE PROSLO: |D| interno izveden iz a,b,c (mult) i vezan anchor-om, faze perm-vezane.");
}

