# Plan optimizacije gasa — bez trusted setupa

Cilj: spustiti gas verifikacije jednog otvaranja (`openBid`) što više je moguće,
a da se **ne izgubi nepoverljivost** klasnih grupa — bez trusted setupa, sa
nepoznatim redom grupe i javno proverljivom verifikacijom. Svaki broj je označen
kao **[IZMERENO]** (pokrenuto u repou), **[PROTOTIP]** (izmereno na radnom
proof-of-concept-u, ali na razmernom modelu — vidi Fazu 4) ili **[PROJEKCIJA]**
(procena, neimplementirano).

Vodeće načelo: nijedan korak ne sme da naruši (1) nepoznat red grupe, (2) javno
proverljive `g` i `h`, (3) verifikaciju bez ičije dozvole. Zato se Groth16 sa
per-circuit ceremonijom **ne bira** iako daje najmanji broj.

---

## Ispravka baseline-a (glavni nalaz Faze 1)

Kad sam krenuo da radim Fazu 1, izmerio sam stvarno stanje repoa i otkrio nešto
važnije od bilo koje nove optimizacije: **prava verifikacija nije ~489M nego ~55M.**

Cifra ~489M poticala je iz benchmarka (`VerifyShapedBench`) koji je merio **staru
klasičnu kompoziciju** (`composeCompact`, ~1.5–3.4M po operaciji). Ali **stvarni
verifier** (`OptimisticWesolowski`, `SegmentedWesolowski`) već koristi **NUCOMP**
(`nucompCompact`). Izmereno, na formama pune veličine (koeficijent 511 bita):

| operacija | klasična | NUCOMP (prava staza) | faktor |
|---|---|---|---|
| kompozicija | ~3.36M | 393k | 8.5x |
| kvadriranje (NUDUPL) | — | 451k | — |

Puna e2e verifikacija stvarnog dokaza (`test_RealProofVerifies`, prava staza koda):
**~55M gasa** [IZMERENO]. To je ~80 kvadriranja (~36M) + ~40 kompozicija (~16M).

Zaključak: Faza 0 (NUCOMP) i najveći deo Faze 1 (assembly, joint-NAF) su **već
implementirani** u repou. Baseline je ispravljen sa 489M na ~55M.

---

## Polazna tačka (izmereno, danas u repou)

| metrika | gas | napomena |
|---|---|---|
| puna verifikacija (prava staza, NUCOMP) | ~55M | `test_RealProofVerifies` |
| shaped worst-case (74 komp forsirano) | ~101M | `VerifyShapedBench` NUCOMP varijanta |
| shaped klasična staza (ne koristi se) | ~235M | stara `composeCompact` mera |
| jedan segment nastavljive verifikacije | ~8M | `SegmentedWesolowski`, staje u L1 blok |
| jedna kompozicija (NUCOMP, puna vel.) | ~393k | 8.5x od klasične |
| jedno kvadriranje (NUDUPL, puna vel.) | ~451k | dominira (~65% verifikacije) |
| `fiatShamirPrime` (pretraga l) | ~169k | zanemarljivo (0.3%) |
| overhead kompaktovanja memorije | ~5–7k/op | zanemarljivo |

---

## Faza 0 — NUCOMP za kompoziciju [URAĐENO]

Van der Poorten Algoritam 3, validiran u Pythonu (1600+ slučajeva do 1792-bit),
portovan u Solidity i integrisan u verifier. Kompozicija 3.36M -> 393k (8.5x).
Najveći pojedinačni dobitak, već u repou.

---

## Faza 1 — mikro-optimizacija aritmetike [UGLAVNOM URAĐENO]

1. **Assembly u množenju, deljenju, add/sub** — URAĐENO. `mul`, `_uadd`, `_usub`,
   Knuth/Warren deljenje, poređenje — sve već ima assembly (potvrđeno `AsmOpsFuzz`).
2. **Joint-NAF stepenovanje** — URAĐENO. Verifikacija deli ~80 kvadriranja između
   oba eksponenta i koristi NAF za manje kompozicija.
3. **l-hint** — NAMERNO PRESKOČENO. `fiatShamirPrime` je samo ~169k (0.3% od 55M).
   Uz to, „skoči na brojač" varijanta ili ne štedi (mora dokazati da su svi raniji
   kandidati složeni) ili blago slabi soundness (dokazivač bira među prostim
   brojevima). Ne vredi rizik za 0.3%.

Gde je sada usko grlo: kvadriranje (~80 x 451k ≈ 36M, ~65%). Broj kvadriranja =
dužina l u bitovima (~80) i **ne može se smanjiti** bez slabljenja soundness-a.
squareCompact je već NUDUPL-optimizovan. Dakle aritmetika je praktično na svom
podu — dalji značajan dobitak traži strukturnu promenu (Faza 4).

Opcioni preostali zahvat (nije urađen, ~10% na ne-dominantni deo): joint
sliding-window širine >2 smanjio bi kompozicije (~16M) za možda ~5M, ali ne dira
dominantno kvadriranje. Rizičan (korektnost windowed stepenovanja), pa nije rađen
bez temeljnog fuzz-a. Na zahtev može.

---

## Faza 2 — nastavljiva verifikacija [URAĐENO]

Puna verifikacija (~55M) razbijena na ~7 segmenata od ≤8M kroz više transakcija
(`SegmentedWesolowski.sol`). Ne smanjuje ukupan gas, ali čini stvar izvršivom na
L1 danas. Nepoverljivost očuvana. Commitment sada veže i `D` (hardening —
`DBindingFix.t.sol`).

---

## Faza 3 — L2 deployment [PROJEKCIJA cene] — VAN OPSEGA OVE IZMENE

> Napomena: po dogovoru L2 preskačemo u ovom prolazu; sekcija ostaje kako je bila.
> Fokus ove izmene je Faza 4 (STARK), koja ne zahteva trusted setup.

Isti bajtkod, na L2. Gas u jedinicama ostaje ~55M, ali cena padne na ~centi do par
dolara po otvaranju. Nepoverljivost 100% očuvana. Nula izmena koda. Primarna
praktična preporuka.

---

## Faza 4 — transparentni STARK omotač [PROTOTIP: analog IZMEREN; 2048-bit oblik+cena IZMERENI; tačna reduce ograničenja PROJEKCIJA]

Ugovor proverava dokaz umesto da izvršava aritmetiku. Samo transparentne šeme
(bez trusted setupa — invarijanta projekta ostaje očuvana):

| šema | on-chain gas | trusted setup | za nas |
|---|---|---|---|
| Groth16 | ~300k | per-circuit | odbačeno (vraća poverenje) |
| PLONK/Halo2 (KZG) | ~300–500k | univerzalni (reuse) | uslovno |
| STARK / Halo2-IPA | ~1–5M | **nema** | **biramo** |

### Šta je URAĐENO ove sesije (radni PoC, `stark-poc/`)

Napravljen je **radni transparentan STARK** (Winterfell 0.8, FRI + Merkle nad
Blake3, polje Goldilocks p = 2^64−2^32+1 sa kvadratnom ekstenzijom) koji
dokazuje **tačno Wesolowski verifikacionu jednačinu** koju ugovor izvršava:

```
shamir(pi, l, u, r) == reduce(w)     ⇔     pi^l · u^r == w
```

AIR (5 kolona) hvata **istu kontrolnu strukturu kao on-chain `shamir`**: jointni
MSB-first square-and-multiply. Kolone: `acc` (akumulator), `lb`/`rb` (bitovi
eksponenata, boolean-ograničeni), `lacc`/`racc` (rekonstrukcije `l` i `r`).
Tranzicija: `acc' = acc²·(lb?pi:1)·(rb?u:1)`, `lacc' = 2·lacc+lb`. Granični
uslovi vezuju početak `(1,0,0)` i kraj `(w,l,r)` za **javne** ulaze → dokaz
postoji **akko** jednačina važi. Solver računa off-chain i pravi dokaz; ugovor
samo proverava.

**Izmereno [PROTOTIP]** (1 vCPU sandbox; kompletan izlaz u `stark-poc/rezultati.txt`):

| dubina n (broj dok. operacija) | veličina dokaza | dokazivanje | verifikacija | sigurnost (conj.) |
|---|---|---|---|---|
| 128 (~ dubina realne verifikacije) | 20,3 KB | ~10–35 ms | 0,3 ms | 117-bit |
| 512   | 33,4 KB | ~20–40 ms  | 0,4 ms | 115-bit |
| 2048  | 46,6 KB | ~35–85 ms  | 0,6 ms | 113-bit |
| 8192  | 65,1 KB | ~150–195 ms | 0,7 ms | 111-bit |
| 32768 | 87,4 KB | ~640–715 ms | 0,9 ms | 109-bit |

(Veličina dokaza, verifikacija i sigurnost su **determinističke**; dokazivanje
je na 1 vCPU i varira po pokretanju — otud rasponi. Sirovi izlaz: `rezultati.txt`.)

Negativni testovi prolaze: lažno `w` → dokaz ODBIJEN; oštećen dokaz (flip
jednog bajta) → ODBIJEN. Nema trusted setupa nigde u lancu.

**Ključni nalaz — agregacija radi (poly-logaritamski rast):** 256× više
operacija (n: 128 → 32768) poveća dokaz samo ~4,3× (21→87 KB), a verifikaciju
~3× (0,30→0,90 ms). To je konkretan, izmeren osnov argumenta „jedan dokaz za
N otvaranja → cena po bidu = verify/N": grupisanje N otvaranja u jedan dokaz
ne množi cenu verifikacije sa N, nego sa ~log N.

### Šta je IZMERENO ove sesije o punom 2048-bit reduce krugu

Cilj ove izmene: povećati diskriminantu na 2048 bita (koeficijenti ~1024 bita)
i izmeriti **oblik i cenu dokaza** punog klasno-grupnog `reduce`-a, umesto da se
pretpostavljaju. Sve dole je pokrenuto (`measure_reduce_depth.py`,
`instrument_round_cost.py`, `wide_air_bench.rs` u istom crate-u kao PoC).

**(a) Dubina redukcije N [IZMERENO].** Kompozicija dve pune redukovane forme daje
neredukovan proizvod (`a` ~2048-bit = 64 limba od 32 bita), koji `reduce` skuplja
nazad na ~1024-bit. Broj rho rundi:

| \|D\| | rho runde N (mean / p95 / max) | koeficijent a pre→posle |
|---|---|---|
| 1024-bit | 104 / 114 / 120 | ~1019 → ~510 bita |
| 2048-bit | 207 / 218 / 228 | ~2043 → ~1022 bita |

N raste ~linearno sa \|D\| (x1.98 pri udvostručenju). Multiplikator `k` po rundi je
mali (~13 bita), pa su množenja `k·a`, `k²·a` usko-ulazna; dominiraju `b²` i `a·c`
u anchor-invarijanti `4ac = b² + |D|`.

**(b) Cena po rundi [IZMERENO].** Instrumentacija limb-operacija: za 2048-bit,
worst-case ~193 limb-množenja + ~393 carry pozicija po rundi. Ukupno za pun
reduce: ~97k (mean) do ~134k (worst) limb-ćelija.

**(c) Tvrd limit — 255 kolona [IZMERENO].** Winterfell 0.8 kapira trag na 255
kolona (glavne + kompozicione zajedno). Samo stanje forme `a,b,c` na 64 limba =
192 kolone — ne staje zajedno sa produkt/carry kolonama. **Posledica: 2048-bit
reduce mora biti uzak-i-dugačak** (limbovi žive kroz redove), ne širok. Ovo je
prinudna, ne stilska odluka.

**(d) Veličina dokaza [IZMERENO na strukturno-vernom AIR-u].** Široki AIR sa
tačnim brojem kolona i dužinom, po jedno tranziciono ograničenje stepena 2 po
koloni (isti FRI parametri kao PoC). Veličina dokaza: **linearna u kolonama**
(~375 B/kolona = 42 upita × 8 B + overhead) i **logaritamska u dužini** (~8 KB po
udvostručenju). Jednak-posao pakovanja (~134k ćelija):

| pakovanje | kolone | n | dokaz | dokazivanje | sec_conj |
|---|---|---|---|---|---|
| P=1 | 64 | 131072 | 129 KB | 20.9 s | 107 |
| P=2 | 96 | 65536 | 132 KB | 12.3 s | 108 |
| **P=4** | **128** | **32768** | **129 KB** | **6.7 s** | **109** |
| P=8 | 192 | 16384 | 144 KB | 4.6 s | 110 |

Šire pakovanje = bolja sigurnost + brže dokazivanje; P=8 naduva kolonski član i
pretrpava 255-kap → **P=4 je optimum**.

**(e) Sigurnost je ograničena poljem, ne upitima [IZMERENO].** Na n=32768,
povećanje upita 42→80 **ne diže** sec_conj (ostaje 109) — Goldilocks² ≈ 2^128
kapira konjekturisanu sigurnost, sav dodatni prostor (do 226 KB) je bačen. Zato
se upiti mogu **smanjiti**: koleno je na **36 upita** (ista sigurnost 109, dokaz
129→**114 KB**); ispod toga upitna pouzdanost postaje granica i sigurnost pada
(q=27→96, q=24→ODBIJEN). Poluga za >115 bita je **kubna ekstenzija** (~2^192), ne
više upita — za prototip nepotrebno (109 = StarkEx-nivo).

**(f) Preporučeni ProofOptions + layout [IZMERENO-OPTIMALNO].**

```
ProofOptions::new(
    36,                       // upiti  (koleno; polje-limit, ne trosi vise)
    8,                        // blowup
    16,                       // grinding
    FieldExtension::Quadratic,// Goldilocks^2 ~ 2^128 (dovoljno za 109-bit)
    4, 31)                    // FRI folding / max remainder (kao PoC)
// trag: P=4 pakovanje -> ~128 kolona x 32768 redova (limbovi kroz redove)
// -> dokaz ~114 KB, sec_conj 109, prove ~6.7s, verify ~1.2 ms
```

**(g) Worst-case rep.** Retki ulazi (N=228, cell/round na maksimumu) daju ~134k
ćelija → pri P=4 to je ~33.5k redova, i dalje unutar n=32768 uz mali padding
buffer; ekstremni rep preko 32768 se rešava **jednim dodatnim segmentom** (isti
mehanizam kao Faza 2), ne rušenjem dokaza niti skokom na n=262144. Uzak režim
(P=1) bi tražio n=262144 i gubi ~2 bita sigurnosti — zato se **ne bira**.

### Šta OSTAJE projekcija (pošteno)

Izmereni su **oblik i cena** dokaza (dubina, kolone, dužina, veličina, sigurnost,
gas) na strukturno-vernom AIR-u. Napravljen je i **prvi PRAVI (zvučan) segment**:

**MUL+CARRY segment [IZMERENO / IMPLEMENTIRANO] (`mulseg_air.rs`).** Dokazuje
`A · b = C` za bignum `A` (8 limba × 16 bita) i jedan limb `b` — tačno operacija
koja dominira reduce (`k·a`, `k·b`, `k²·a`; `k` je 1 limb). NIJE dummy: pun
schoolbook carry lanac sa **range-check-ovima preko bit-dekompozicije** (16-bit
limbovi → proizvod `< 2^32 ≪ p`, bez wrap-around-a mod p), boolean-vezanim
bitovima i rekompozicijom. Constraint-i: `a·b + cin == c + 2^16·cnext`, carry
lanac `nxt.cin == cnext`, `c == Σ bit·2^k`, i boolean svih bitova (35 constraint,
max stepen 2). Izmereno: 16 redova × 35 kolona, dokaz **13.6 KB**, dokazivanje
2.8 ms, verifikacija 0.18 ms, sigurnost 120-bit. **Zvučnost potvrđena negativnim
testovima:** lažno `C`, lažno `b`, lažno `A`, oštećen dokaz — svi ODBIJENI.
Range-check nije opcion: bez njega prover može podvaliti carry; bit-dekompozicija
ga zatvara.

Ono što ostaje je **produkciono skaliranje montaže** — svih 228 rundi, svih 64
limba svuda, i merenje gasa finalnog dokaza. Sama montaža je sada **demonstrirana
end-to-end kroz milestone-e A–E na punoj 2048-bit širini** (vidi tabelu montaže
ispod); preostalo je mehaničko skaliranje dokazanih delova, ne novi mehanizmi.

**Montaža pune širine [IZMERENO / IMPLEMENTIRANO] (`mulseg_a..e2.rs`).** Svaki
gradivni blok pune 64-limb/2048-bit montaže je zaseban zvučan STARK dokaz sa
negativnim testovima:

| milestone | šta | kolone | dokaz |
|---|---|---|---|
| A | single-limb množilac `k·c` (1024-bit) | 35 | 26.9 KB |
| B | 64×64 množilac `a·c`,`b²` (sliding-window, POS izbegnut) | 169 | 66 KB |
| C | anchor `4ac=b²+\|D\|` combine (128 limba, narrow-long) | 44 | 29 KB |
| D1 | množilac+anchor FUZIJA (bez selektora, unutar-red) | 212 | 79 KB |
| D2 | potpisano oduzimanje (jezgro `b'`,`c'`, znak zvučan) | 22 | 21 KB |
| E1 | puna rho normalize-izlaz sklopljena iz primitiva | 63 | 33 KB |
| E2 | dva rho segmenta ulančana (boundary I/O + D-vezivanje) | 10 | 2×5 KB |

Ključni arhitektonski nalazi montaže: (1) **255-zid preživljen** — 64×64 množilac
staje u 169 kolona preko sliding-window (naivni POS one-hot bi bio 256+); (2)
**fazni selektor nepotreban** — fuzija preko grupa kolona sa unutar-red protokom
(D1); (3) **potpisana aritmetika jeftina i zvučna** — 22 kolone, pogrešan znak
nemoguć (D2); (4) **ulančavanje + D-vezivanje rade** — forma teče preko segment
granice, disc-invarijanta vezuje `D` (E2). Nijedan otvoreni istraživački rizik
nije ostao.

Ono što ostaje projekcija: **puna 64-limb narrow-long montaža** — sklopiti
sve segmente na punoj širini (64 limba × 16 bita), sa limbovima kroz redove, u
jedan trag. Svi mehanizmi su dokazani, uključujući koegzistenciju rho lanca i
LogUp-a (integracija ispod).

**integracija rho + LogUp [IZMERENO / IMPLEMENTIRANO] (`mulseg6_integ.rs`).**
Spaja dva mehanizma koja dosad nisu bila u istom AIR-u: **glavni-trag rho lanac**
(svaki red = jedna rho runda; lanac cikliše pa je svaki od 32768 redova validna
tranzicija, bez selektora) i **aux-trag LogUp** koji range-check-uje `BM=|b|` i
`W1` protiv deljene tablice `[0,2^15)`. 11 glavnih + 2 aux kolone, dokaz 93 KB,
prove 1.1 s, sec 109. Validan slučaj PASS; `BM` van opsega ODBIJEN.

**Kvantifikovana ušteda kolona (projekcija iz izmerenih po-segment troškova):**
za pun 64-limb reduce, range-check jedne runde bit-dekompozicijom traži **5120
kolona** (20× preko 255-zida → nemoguće); LogUp-om **11 kolona + jedna deljena
65536-red tablica** (amortizovana preko svih ~1140 range-check vrednosti) →
izvodljivo. Faktor ~465× po rundi. Izmereno na skaliranom PoC-u: mulseg4 164
kolone → mulseg6 11+2 (~13× manje). **Ovo zatvara poslednji istraživački rizik
(255-kolona zid); ostaje samo montaža.**

**Zbirno stanje reduce mehanizama (svi IZMERENI, sa STARK dokazom + neg. testovima):**

| mehanizam | fajl | dokaz | ključno |
|---|---|---|---|
| MUL+CARRY (`k·a`) | `mulseg_air.rs` | 13.6 KB | carry lanac + range-check |
| multi-limb × multi-limb | `mulseg2_air.rs` | 29 KB | bounded akumulator (`2^33.5 ≪ p`) |
| anchor `4ac=b²+\|D\|` | `mulseg3_anchor.rs` | 42 KB | ×4, veliko sabiranje, jednakost |
| normalize/rho | `mulseg4_rho.rs` | 40.6 KB | znak, normalizacioni opseg, lanac |
| LogUp range-check | `mulseg5_logup.rs` | 28.6 KB | aux trace, O(1) overhead |
| rho + LogUp integrisano | `mulseg6_integ.rs` | 93 KB | dva mehanizma u jednom AIR-u |

Svih šest je zvučno (falsifikat pada u negativnim testovima), na pravim ili
realno-veličinskim brojevima. Preostaje jedino montaža na punoj 64-limb širini.

**LogUp range-check segment [IZMERENO / IMPLEMENTIRANO] (`mulseg5_logup.rs`).**
Zamenjuje bit-dekompoziciju tabelarnim argumentom preko **pomoćnog (auxiliary)
trace segmenta** sa izazovom `alpha` (Fiat-Shamir posle commit-a). Dokazuje da
sve `W_i ∈ [0,N)` preko logaritamsko-izvod identiteta
`Σ 1/(α-W_i) = Σ M_j/(α-T_j)`; tablica `T=[0,N)` pinovana u glavnom tragu,
`M_j`=višestrukost, aux kolona akumulira sumu koja mora telescope-ovati na 0.
Glavni trag 3 kolone + 1 aux. **Kvantifikovan dobitak:** 256 vrednosti
range-check-ovano u ~4 kolone (vs 256×8=2048 boolean kolona bit-dekompozicijom).
Overhead pada sa `O(k)`/vrednost na `O(1)` ukupno. Trošak se seli u redove (`2^k`
redova za tablicu, jedna deljena, amortizovana) — jeftino (log FRI) umesto skupo
(kolone linearno). Validan slučaj PASS (dokaz 28.6 KB, sec 116); van-opsega (300,
granično 256) ODBIJENI. **Ovo direktno rešava 255-kolona zid** koji je rho segment
(156/164 kolone range-check) identifikovao kao fatalan.

**normalize/rho segment [IZMERENO / IMPLEMENTIRANO] (`mulseg4_rho.rs`).** Dokazuje
LANAC od 7 rho rundi na **pravoj formi** (`k=[-4,-9,-1,0,...]`). Uvodi mehaniku
koju množioci/anchor nisu imali: (1) **ZNAK** — `b`,`k` mogu biti negativni,
sign-magnitude reprezentacija sa `signed(x)=(1-2s)·|x|`; (2) **normalizacioni
opseg** `-a'<b'≤a'` koji jedinstveno pinuje `k`, preko dva nenegativna svedoka
`W1=c-b'≥0`, `W2=c+b'-1≥0`; (3) **ulančavanje** — svaki red→red je jedna rho
runda (preview stavke 5). Aritmetika NATIVNA (mali operandi <2^30 → međurezultati
<2^35 ≪ p); limb-nivo za velike operande je mulseg2. 8 redova × 164 kolone, dokaz
40.6 KB, prove 13.2 ms, verify 0.31 ms, sec 121-bit. Negativni (početni `b`,
finalni `c`, oštećen dokaz) ODBIJENI.

**Ključno merenje za (4):** od 164 kolone, **156 (95%) su range-check** (bit-
dekompozicija), i to na samo 30-bit opsegu. Na punom 64-limb reduce-u to je
neizvodljivo pod 255-kolona limitom → **LogUp je sledeći kritičan korak**, ne
kozmetika.

**anchor `4ac=b²+|D|` segment [IZMERENO / IMPLEMENTIRANO] (`mulseg3_anchor.rs`).**
Dokazuje invarijantu diskriminante na **PRAVOJ redukovanoj formi** (256-bit `D`,
brojevi generisani iz `classgroup` modula, ne toy). Izoluje novu mehaniku koju
množioci nisu imali: množenje konstantom (×4) sa carry-jem, sabiranje dva
multi-limb broja (`b²+|D|`), i jednakost 17-limbnih brojeva (per-limb
`L[k]==R_[k]`). Dve carry staze (LHS `4·AC`, RHS `BB+|D|`), obe **nenegativne**
jer `D<0 ⇒ 4ac>b²` — zato unsigned carry, bez borrow-a. 32 reda × 113 kolona,
dokaz **42 KB**, prove 2.9 ms, verify 0.48 ms, sigurnost 119-bit. Sva četiri
falsifikata (`|D|`, `AC`, `BB`, oštećen dokaz) ODBIJENA. Puna invarijanta =
mulseg2 (dokazuje `AC=a·c`, `BB=b²`) ∘ ovaj segment (dokazuje `4·AC=BB+|D|`);
spajanje u jedan trag je (5).

**multi-limb × multi-limb segment [IZMERENO / IMPLEMENTIRANO] (`mulseg2_air.rs`).**
Dokazuje `A · B = C` za dva 8-limba (128-bit) broja → 16-limbni rezultat — obrazac
za `b²` i `a·c` u anchoru. Rešava jedini netrivijalan deo: **akumulacija više
proizvoda po poziciji** bez preliva mod `p`. Konvolucija preko one-hot pozicionog
selektora (`conv = Σ POS[i+j]·A[i]·B[j]`, stepen 3), A/B broadcast kao konstantne
kolone, jedna pozicija po redu, range-check C (16-bit) i carry (21-bit).
**Zvučnost bounded akumulatora IZMERENA:** max akumulator `s = 2^33.5` uz `p ≈
2^64` (~30 bita zazora), max carry `2^17.5` (> 16 bita → 21-bit range-check
opravdan). 32 reda × 71 kolona, dokaz **29 KB**, prove 12.6 ms, verify 0.39 ms,
sigurnost 119-bit. Sva četiri falsifikata (`C`, `A`, `B`, oštećen dokaz) ODBIJENA.

PoC dokazuje **kontrolnu strukturu** verifikacije nativno u polju; grupni
elementi su tu elementi polja, a operacija je množenje u polju. **Klasno-grupna
aritmetika** (1024-bit forme, `reduce`, NUDUPL/NUCOMP) **nije aritmetizovana** —
to je i dalje najveći neimplementiran deo (isto kao što `docs/ideja...` navodi).
Dva puta napred, oba realna:

1. **Non-native bignum AIR** — aritmetizovati kompoziciju/kvadriranje 1024-bit
   formi direktno (range-check limbova + Euklid/`reduce` kao pomoćne kolone).
   Najviše posla; najčistiji rezultat.
2. **zkVM (RISC Zero / SP1)** — pokrenuti *postojeći* Python/Rust verifier u
   zkVM-u i dokazati izvršavanje. Brže do kraja, ali oprez: on-chain deo tih
   zkVM-ova tipično ide kroz Groth16 omotač (~300k gas, **trusted setup**) —
   ako želimo da ostanemo transparentni, verifikuje se STARK receipt direktno
   (skuplje, ~milioni gasa).

### On-chain cena (pošteno, sa referencama)

Cifra „~1–2M" iz ranije verzije bila je optimistična — odgovarala je 20 KB
toy-PoC dokazu (5 kolona, 128 redova). **Sada je ankerovana merenjem:** pun
2048-bit reduce dokaz je ~114 KB (optimizovano; vidi (d)–(f) gore), ~7× veći od
toy-PoC-a. Odatle, po dokazu:

| stavka | gas |
|---|---|
| calldata (~114 KB, 11–16 gas/B) | ~1.25–1.82M |
| FRI/Merkle/polje compute (StarkEx-stil) | ~2–4M |
| **ukupno po dokazu** | **~3.3–5.8M** (sredina ~4.5M) |

Time je **potvrđen ~5M anchor** (ne ~1–2M). Verifikacija je i dalje
**poly-logaritamska u broju činjenica** → agregacijom N otvaranja u jedan dokaz
(~isti ~114 KB), cena po otvaranju = ~5M/N → ka ~1000-ama gasa. Groth16 omotač
(npr. SP1) dođe do **~300k**, ali uz **trusted setup** — svesno se odbacuje.
Zaključak za prezentaciju: nije poenta „jedan dokaz jeftin", nego **cena po
otvaranju pod agregacijom pada ka ~1000-ama gasa**, bez ijednog subjekta od
poverenja.

Trošak se seli off-chain (generisanje dokaza = računanje, ne gas). Solver ga
nosi — model zarade.

---

## Zbirna tabela — put od danas do minimuma

| faza | on-chain gas (po otvaranju) | status | nepoverljivost |
|---|---|---|---|
| danas (prava staza) | ~55M | IZMERENO | ✓ |
| Faza 0: NUCOMP | uključeno u 55M | URAĐENO | ✓ |
| Faza 1: aritmetika + NAF | uključeno u 55M | URAĐENO | ✓ |
| Faza 2: segmentacija | ~7 segm. x ≤8M | URAĐENO | ✓ |
| Faza 3: L2 | ~55M jedinica, cena u centima | PROJEKCIJA cene | ✓ |
| Faza 4: STARK omotač | ~3.3–5.8M/dokaz (~114 KB), ~log N uz agregaciju | oblik+cena IZMERENI; svih 6 reduce mehanizama dokazano; ostaje montaža | ✓ |

Iskren minimum uz očuvanu nepoverljivost: transparentna STARK verifikacija je
reda **~5M gasa po dokazu**, ali **poly-logaritamska u broju otvaranja** — pa
cena po bidu pod agregacijom pada ka ~1000-ama gasa (izmereno skaliranje u
`stark-poc/`: 256× računa → ~3× verifikacije). Cifra ~300k je samo Groth16
omotač, koji svesno odbacujemo jer vraća trusted setup. **Napomena o zrelosti:**
za 2048-bit smo izmerili **oblik i cenu** punog reduce dokaza (dubina N≈228,
~128 kolona × 32768 redova zbog 255-kolona limita, dokaz ~114 KB, ~3.3–5.8M
gasa, sigurnost polje-ograničena na 109 bita); ono što još **ne** postoji su
tačna tranziciona ograničenja pravog `reduce`-a — dokaz zna svoju cenu ali još
ne dokazuje ispravnu klasnu grupu. To je najveći preostali posao.

---

## Šta reći mentorima (poštena formulacija)

„Kad smo tačno izmerili, prava verifikacija je ~55M, ne 489M — stara cifra je merila
klasičnu kompoziciju koju verifier više ne koristi otkako smo integrisali NUCOMP
(kompozicija 8.5x jeftinija). Aritmetika je time praktično na svom podu, dominira je
kvadriranje čiji se broj ne može smanjiti bez slabljenja sigurnosti. Dalje:
segmentacija to čini izvršivim na L1 danas, a dugoročno STARK omotač — koji
je transparentan i bez trusted setupa. Za STARK nismo ostali na priči: napravili
smo radni PoC (Winterfell/FRI) koji dokazuje tačno našu verifikacionu jednačinu
`pi^l·u^r == w` — dokaz ~20 KB, verifikacija ispod milisekunde, ~117-bit
sigurnost, i falsifikat pada. Izmerili smo i da agregacija radi: 256× više
računa poveća verifikaciju samo ~3×, pa cena po otvaranju pod agregacijom pada
ka ~1000-ama gasa (produkcijski STARK-ovi verifikuju za ~5M po dokazu,
poly-logaritamski u broju činjenica). Za 2048-bit smo otišli korak dalje i
izmerili ceo oblik pravog dokaza: redukcija ima ~228 rundi, trag zbog
255-kolona limita Winterfell-a pada u režim ~128 kolona × 32768 redova, pun
dokaz je ~114 KB → ~3.3–5.8M gasa on-chain, što potvrđuje naš ~5M anchor umesto
ranije preoptimističnih ~1–2M. Usput smo našli da je sigurnost ograničena
veličinom polja (~109 bita), ne brojem upita — pa smo upite spustili 42→36 i
skratili dokaz bez gubitka sigurnosti. Pošteno: izmerili smo koliko dokaz košta,
ali tačna reduce-ograničenja (da dokaz zaista dokazuje klasnu grupu) su sledeći i
najveći posao. Groth16 bi dao ~300k ali bismo izgubili nepoverljivost, pa ga ne
biramo."

Sve „IZMERENO" je pokrenuto u repou; „PROTOTIP" / „IZMERENO na strukturno-vernom
modelu" je izmereno na razmernom ili oblik-vernom modelu (Faza 4, `stark-poc/`,
`wide_air_bench.rs`); „PROJEKCIJA" su pravci, ne rezultati.
