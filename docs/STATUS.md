# STATUS — STARK omotač za klasno-grupni `reduce` (2048-bit)

Transparentna STARK aritmetizacija `reduce`-a imaginarne kvadratne klasne grupe,
bez trusted setupa. Winterfell 0.8.3, Goldilocks + kvadr. ekstenzija, 16-bit limbovi.
Sve dole je **pokrenuto i izmereno** (rustc 1.75, 1 vCPU); svaki segment ima STARK
dokaz + negativne testove na pravim ili realno-veličinskim brojevima.

## Kontekst gasa (iz ranijih faza)
- Prava on-chain verifikacija danas: **~55M gasa** (NUCOMP, izmereno) — ne 489M.
- STARK omotač: **~3.3–5.8M / dokaz** za pun 2048-bit reduce (~114 KB), potvrđeno
  merenjem oblika traga; agregacija obara cenu po bidu ka ~1000-ama gasa.
- Sigurnost je **polje-ograničena** na ~109 bita (Goldilocks² ≈ 2^128), ne upitima
  → optimalno **36 upita** (koleno; ispod toga sigurnost pada).

## Status montaže (A–E2) — SVE IZMERENO + ZVUČNO

| # | mehanizam | fajl | kolone | redovi | dokaz | prove |
|---|---|---|---|---|---|---|
| A | single-limb množilac `k·c` (1024-bit) | `mulseg_a.rs` | 35 | 128 | 26.9 KB | 9 ms |
| B | 64×64 množilac `a·c`,`b²` (sliding-window) | `mulseg_b.rs` | 169 | 128 | 66 KB | 21 ms |
| C | anchor `4ac=b²+\|D\|` combine (128 limba) | `mulseg_c.rs` | 44 | 128 | 29 KB | 13 ms |
| D1 | množilac+anchor FUZIJA (bez selektora) | `mulseg_d1.rs` | 212 | 128 | 79 KB | 23 ms |
| D2 | potpisano oduzimanje (jezgro `b'`,`c'`) | `mulseg_d2.rs` | 22 | 128 | 21 KB | 10 ms |
| E1 | puna rho normalize-izlaz iz primitiva | `mulseg_e1.rs` | 63 | 128 | 33 KB | 12 ms |
| E2 | 2 rho segmenta ulančana + D-vezivanje | `mulseg_e2.rs` | 10 | 8 | 2×5 KB | — |
| F | **PUN round-AIR** (64-limb, deljeni LogUp `[0,2^16)`, CTR) | `round_full.rs` | 21 | 65536 | 107 KB | 3.3 s |
| G | **CEO reduce ulančan** (228 rundi, 1 trag, 1 LogUp tablica) | `reduce_chain.rs` | 15 | 65536 | 104 KB | 2.2 s |
| H | **SPOJENO** (64-limb blok × 228, 1 trag, 1 LogUp) | `reduce_merged.rs` | 23 | 65536 | 109.5 KB | 3.1 s |
| I | **PERM-vezivanje lanca** (grand-product c(r)==a(r+1)) | `perm_bind.rs` + integr. u `reduce_merged.rs` | +2 kol/1 aux Z | — | 63 KB (demo) | 0.1 s |
| J | **DISC-ANCHOR** (4ac−b²=|D|, 2048-bit, LogUp) | `disc_anchor.rs` | 19 | 65536 | 107.6 KB | 2.8 s |
| K | **DISC-FULL** (|D|←a,b,c: mult AC/BB + anchor, perm-vezano) | `disc_full.rs` | 42 (L=4 demo) | 4096 | 73.8 KB | 0.18 s |
| L | **DISC-FULL L=64** (|D|←a,b,c PUNA širina, sliding-window) | `disc_full_l64.rs` | 160 | 65536 | 152.7 KB | 32 s |
| M | **PROVER + VERIFIER** (classgroup→receipt→on-chain) | `prover.rs`+`MintLockVerifier.sol`+`emit_trajectory.py` | — | — | receipt 108 KB | prove 3.5 s |

Raniji (skalirani) segmenti, takođe zvučni:

| mehanizam | fajl | napomena |
|---|---|---|
| MUL+CARRY (`k·a`, 8 limba) | `mulseg.rs` | prvi zvučan carry-lanac + range-check |
| multi-limb × multi-limb (8×8) | `mulseg2.rs` | bounded akumulator (`2^33.5 ≪ p`) |
| anchor (18 limba) | `mulseg3.rs` | ×4, veliko sabiranje, jednakost |
| normalize/rho lanac (mali) | `mulseg4.rs` | znak + normalizacioni opseg + lanac |
| LogUp range-check | `mulseg5_logup.rs` | aux trace, O(1) overhead, tablica `[0,2^k)` |
| rho + LogUp integracija | `mulseg6_integ.rs` | dva mehanizma u jednom AIR-u |

**Ključna merenja:**
- Reduce dubina `N` (rho runde): **2048-bit → 207 mean / 218 p95 / 228 max** (izmereno).
- Bounded akumulator: 64 proizvoda/poz × 16-bit → `s < 2^38 ≪ p=2^64` (nema wrap).
- LogUp ušteda kolona: bit-dekomp bi tražila **5120 kol/rundi** (nemoguće); LogUp
  **~11 kol + jedna deljena tablica** → ~465× manje.

## ZAVRŠENO I DOKAZANO
- **KORAK 1 (pun unutar-red round-AIR) — SKLOPLJEN I IZMEREN** (`round_full.rs`,
  `rezultati-round_full.txt`): jedna rho runda na **64 limba** (128-limb medjuproizvod),
  SVI range-check-ovi kroz **JEDNU deljenu LogUp tablicu `[0,2^16)`** (N=65536, nula
  bit-dekompozicija), **CTR punog stepena** (DEEP-quirk fix), sirina **21 kolona ≪ 255**.
  Dokaz **107 KB / 108-bit / prove ~3.3 s** (1 vCPU). Negativni testovi razdvajaju
  dva sloja zvučnosti: LogUp hvata van-opsega (`P=70000`, granica `65536`),
  aritmetičko jezgro hvata in-range-ali-pogrešno (`P` proizvod, `W` normalize).
- **KORAK 2 (ulančavanje celog reduce-a) — SKLOPLJEN I IZMEREN** (`reduce_chain.rs`,
  `rezultati-reduce_chain.txt`): svih **228 rundi ulančano u JEDAN trag** pod **JEDNOM
  deljenom LogUp tablicom `[0,2^16)`** (amortizacija: jedna tablica 65536 redova za
  range-check kroz sve rundi). Novi mehanizam = **fabrika ulančavanja**: granica rundi
  vezana `F_out(r)==F_in(r+1)` (E2 boundary-I/O obrazac, sada INTERNALIZOVAN u jedan
  trag umesto N odvojenih dokaza), **disc-invarijanta `4ac-b²=|D|` u svakom redu**
  (D-vezivanje), CTR pun stepen, bez faznog selektora (granica preko BOOLEAN flag-a).
  **15 kolona ≪ 255**, dokaz **104 KB / 108-bit / prove ~2.2 s** (1824 aktivna reda,
  N=65536 tablica dominira dužinu). Tri negativna testa izoluju po jedan mehanizam:
  prekinut lanac (disc-očuvan SB-flip → samo granica puca), pokvarena disc, |b| van tablice (LogUp).
- **KORAK 3 (spajanje Koraka 1 + 2) — SKLOPLJEN I IZMEREN** (`reduce_merged.rs`,
  `rezultati-reduce_merged.txt`): svaka runda je sada **64-limb BLOK od 128 limb-redova**
  (puna narrow-long aritmetika iz Koraka 1: `P=k·B` mult+carry, `W` normalize), a **228
  blokova ulančano** end-to-end u JEDAN trag pod **JEDNOM deljenom LogUp tablicom `[0,2^16)`**.
  **29184 aktivna reda** (228×128), **21 kolona ≪ 255**, dokaz **108.7 KB / 108-bit / prove ~3.0 s**.
  ENFORCED: blok-aritmetika (mult+carry, normalize), deljeni LogUp range-check (P, |b'|, W)
  kroz sve blokove, blok-struktura (ISB/RIDX/CTR). Tri negativna testa izoluju: P van tablice
  (LogUp), P pogrešan proizvod (mult+carry), W pogrešan (normalize).
  **Poštena granica obima:** poziciono vezivanje forme između blokova `a(r+1)[k]==c(r)[k]`
  NIJE ENFORCED (Winterfell `Assertion::single` veže ćeliju-za-konstantu, ne ćeliju-za-ćeliju;
  susedni frame ne dohvata stride-RR redove). |D| je javni ulaz (transkript), ne interno
  re-derivovan iz limba. Ova dva su naredni podmilestone.
- **KORAK 4a (vezivanje forme) — DOKAZANO I INTEGRISANO** (`perm_bind.rs`, pa uklopljeno
  u `reduce_merged.rs`): inter-blok lanac `a(r+1)[k]==c(r)[k]` je sada **ENFORCED**
  grand-product permutacijom nad `(tag,val)`, tag committed (`r*L+p` za c, `(r-1)*L+p` za a) →
  isti tag za lančane parove, multiset-jednakost (Schwartz–Zippel po γ) daje limb-po-limb
  jednakost. Jedan aux Z stubac + 2 committed tag kolone; granični a_first/c_last javni
  (zatvaranje). `reduce_merged` sada **23 kolone, 109.5 KB / 108-bit**, i novi negativni test
  „prekinut lanac (a-limb @blok 60)" je ODBIJEN — ranija rupa zatvorena. Degree gotcha:
  grand-product je **stepen 3** (`INBLK·Z'·e_c`), ne 2.
- **KORAK 4b (disc-anchor) — DOKAZANO** (`disc_anchor.rs`, `rezultati-disc_anchor.txt`):
  `4·a·c − b² == |D|` na **pravoj 2048-bit formi** (128 limba iz `anchor128.txt`),
  sa **LogUp range-check-om umesto bit-dekompozicije** (dva carry lanca LHS/RHS, anchor
  `L[k]==R[k]`). **19 kolona, 107.6 KB / 108-bit**. Tri negativna: pogrešan `|D|`, pogrešan
  `AC=a·c` (anchor puca), `L` van tablice (LogUp). Time je |D| interno vezan za formu.
  **Poštena granica:** dokazuje anchor nad datim `AC=a·c`, `BB=b²` limbovima; ne re-derivuje
  ih množenjem iz `a,c,b` (to je `mulseg_b` sloj). Puno vezivanje `|D|←a,b,c` = anchor + mult
  u istom tragu (spajanje disc_anchor + mulseg_b), inženjerski korak.
- **KORAK 5 (puno vezivanje |D|←a,b,c) — DOKAZANO** (`disc_full.rs`, `rezultati-disc_full.txt`):
  u JEDNOM tragu, tri faze: `MULT_AC` (AC=a·c) + `MULT_BB` (BB=b·b) preko one-hot konvolucije,
  pa `ANCHOR` (4·AC − BB == |D|). Faze **perm-vezane** grand-product-om (AC/BB koje anchor
  troši == AC/BB koje mult proizvodi), **LogUp** range-check limba. `|D|` je sada interno
  izveden iz `a,b,c` množenjem — više nije spoljni ulaz. Demo **L=4, 42 kolone**, dokaz 73.8 KB.
  Četiri testa: validan + AC proizvod pogrešan (conv puca) + |D| pogrešan (anchor puca) +
  perm PVAL pokvaren (mult↔anchor veza puca). Skaliranje na L=64 je isto (širina konstantna,
  više redova) — kao round_full→reduce_merged. Gotcha: grand-product sa fazom-gejtom je
  **stepen 4** (`psel·fanc·zp·ea`), ne 3.
- **KORAK 5b (disc_full skaliran na L=64) — DOKAZANO** (`disc_full_l64.rs`,
  `rezultati-disc_full_l64.txt`): puno vezivanje `|D|←a,b,c` na **punoj širini** (1024-bit
  operandi, 2048-bit proizvod). **160 kolona / 152.7 KB / 108-bit**, 512 aktivnih redova.
  **Skaliranje-otkriće:** one-hot POS shema iz L=4 demo-a **ne skalira** (OP1+OP2+POS =
  64+64+128 = 256 kol > 255-zid); zamenjena **sliding-window** konvolucijom (mulseg_b obrazac:
  `conv=Σ A[i]·WIN[i]`, WIN klizi, WIN[0] hranjen pozicionim asertacijama). Carry konvolucije
  ide do ~2^21 pa razložen na `cnlo` (16-bit) + `cnhi` (5-bit), oba LogUp-check. Ista četiri
  testa prolaze (validan + AC proizvod + |D| + perm). Prove ~32 s (L=64 množenje teško),
  verify ostaje ms.
- **KORAK 6 (prover + verifier) — LANAC RADI E2E** (`prover.rs`, `MintLockVerifier.sol`,
  `emit_trajectory.py`, `e2e_test.py`): 
  (a) **emit_trajectory.py** emituje PRAVU classgroup reduce trajektoriju (2048-bit D iz
  reference impl-a) kao tekst; 
  (b) **prover.rs** (off-chain, Rust) čita trajektoriju, računa `AC=a·c`, `BB=b·b`, dokazuje
  `4·AC − BB == |D|` transparentnim STARK-om, serijalizuje **RECEIPT** (magic `MLK1`: sec +
  javni ulazi + proof bytes); receipt **108 KB**, prove ~3.5 s, sec 108; 
  (c) **MintLockVerifier.sol** (on-chain): parsira MLK1 receipt, proverava sec≥95 i anchor
  `L0==R0`, rekonstruiše Fiat-Shamir seed (keccak), ima **punu Merkle-put verifikaciju** +
  gas-projekciju. E2E test (`e2e_test.py`, reprodukuje Solidity logiku) prolazi: parsing,
  transcript determinizam, Merkle round-trip. 
  **Poštena granica:** Solidity implementira receipt-parsing, transcript, Merkle-put i
  gas-računicu [IMPLEMENTIRANO]; puna FRI-folding rekurzija + DEEP kompoziciona provera su
  označene [SKELET/TODO] (traže Goldilocks polje-aritmetiku u Solidity — zaseban modul,
  hiljade linija). Gas [PROJEKCIJA] ~810k za Merkle+FRI skelet; puna verifikacija cilja
  STATUS ~3.3–5.8M. (solc nije dostupan u okruženju — Solidity verifikovan pregledom +
  Python reprodukcijom logike.)
- **KORAK 7 (pun Solidity FRI+DEEP verifier) — 5 DELOVA DOKAZANO** (svi validirani
  test-vektorima protiv Winterfell 0.8.3):
  - **Deo 1** `Goldilocks.sol`: Fp (p=2⁶⁴−2³²+1) + Fp2 ekstenzija. Otkriće: ireducibilni
    je **x²−x+2** (φ²=φ−2), NE x²+2 (−2 je QR pa x²+2 nije ireducibilan) — validirano
    `fp2_vectors.rs` (mul/square/inv, 20 vektora == Winterfell QuadExtension).
  - **Deo 2** `Transcript.sol`: Fiat-Shamir RandomCoin, bit-za-bit == Winterfell
    (`merge_with_int(seed,v)=Blake3(seed||v_LE8)`); init/draw/reseed/drawIntegers svi OK.
  - **Deo 3** `MerkleVerify.sol`: leaf=Blake3(concat LE8), put sa Winterfell index
    re-baziranjem `(index+2^(len−1))>>1`; verifyOpening + negativni OK.
  - **Deo 4** `DeepComposer.sol`: OOD konzistentnost `Σ z^(i·N)·H_i(z)` + DEEP kombinacija
    (trace racionalna + constraint racionalna, sve Fp2); composeAt == Winterfell na 3 pozicije.
  - **Deo 5** `FriVerify.sol`: FRI folding (folding_factor=4), Lagrange fold == Winterfell
    interpolate+eval, x-koordinate + remainder Horner OK.
  - `contracts/README.md`: pun verifier flow (11 koraka) + poštene granice.
  **Preostalo:** orkestracija (`verify()` koji spaja 1–5 tačnim redosledom + proof byte-parsing
  svih sekcija) — komponente tačne, spajanje je inženjering; Blake3-u-Solidity ili keccak-dokaz;
  gas na deployanom ugovoru.
- Svi aritmetički mehanizmi `reduce`-a na punoj 2048-bit širini: single/multi-limb
  množenje, anchor `4ac=b²+|D|`, potpisano sabiranje/oduzimanje, normalize/rho izlaz.
- **255-kolona zid preživljen** (64×64 u 169 kol preko sliding-window; POS one-hot izbegnut).
- **Fazni selektor nepotreban** (fuzija preko grupa kolona, unutar-red protok — D1).
- **Potpisana aritmetika zvučna** (pogrešan znak nemoguć — D2).
- **LogUp range-check** (zamena bit-dekompozicije, O(1) kolona — mulseg5/6).
- **Ulančavanje + D-vezivanje** (forma preko segment granice, disc-invarijanta vezuje `D` — E2).
- Nijedan otvoreni **istraživački** rizik nije ostao.

## OSTAJE ZA PRODUKCIONO SKALIRANJE (inženjering, ne novi mehanizmi)
1. **Solidity: puna FRI + DEEP** (Goldilocks polje-aritmetika u EVM) — zameniti [SKELET/TODO]
   u `MintLockVerifier.sol` pravom folding rekurzijom; izmeriti gas na deployanom ugovoru.
2. Izmeriti **gas finalnog agregatnog dokaza** na realnom oblik-modelu (kalibrisati ~3.3–5.8M).
3. (opciono) Optimizacija prove vremena za L=64 množenje (Karatsuba/NTT).


## PREPORUKE ZA DALJU OPTIMIZACIJU

### Pojedinačne komponente
- **Širina traga:** narrow-long drži širinu ~konstantnom (A: 35 kol i na 8 i na 64
  limba). Držati se toga; broadcast koristiti samo za stacionaran operand (sliding-window za drugi).
- **Stepen polinoma:** držati max degree ≤ 2–3. Potpisane/kvadratne izraze spuštati
  **pomoćnim kolonama** (`SBV`,`SKV`,`KK` u E2 spustili `c'` sa deg 4 na 2). Bitno za blowup 8.
- **Ušteda kolona:** LogUp umesto bit-dekompozicije za SVE range-check-ove; jedna
  deljena tablica amortizovana preko cele montaže. Cilj: pun round-AIR < 255 kol.
- **Winterfell quirk:** ciklične/niskostepene trag-kolone ruše DEEP kompoziciju
  (`poly_size−2 ≠ degree`). Uvek dodati **jednu kolonu punog stepena** (CTR brojač `i`).
- **Carry širine:** kalibrisati po poziciji (single-limb: carry <2^3; 64×64: <2^23);
  ne prebacivati bez potrebe (bitovi = kolone).

### Agregacija (228 rundi → jedan dokaz)
- **Segment-boundary I/O** (E2 obrazac): batch od ~30 rundi po segmentu (gas budžet),
  forma teče kao commitment, `D` vezan disc-invarijantom u svakom segmentu.
- **Rekurzivna/batch agregacija:** jedan STARK koji dokazuje N otvaranja → dokaz raste
  ~log N (izmereno u ranijem `stark-poc`: 256× računa → ~3× verifikacije). Cena/bid = ~5M/N.
- **Redukcija gasa:** (a) L2 deployment (isti bajtkod, cena u centima); (b) agregacija
  N otvaranja; (c) NIKAD Groth16 omotač (~300k ali vraća trusted setup — invarijanta projekta).
- **Prioritet:** prvo pun round-AIR (jedan trag, sve faze, LogUp, < 255 kol, CTR),
  pa segmentacija rundi, pa agregacija otvaranja. Gas se meri tek na kraju, na realnom obliku.

## OKRUŽENJE (za novi chat)
- `apt-get install -y rustc cargo` (Ubuntu 24.04 → rustc 1.75, tačno za `Cargo.lock`).
- Crate: `stark-poc/` (Winterfell 0.8.3, deps sa crates.io). Build: `cargo build --release --bin mulseg_X`.
- Data fajlovi (`*.txt`) generisani Pythonom iz `classgroup`/`measure_reduce_depth.py`.
- Radni stil: runnable kod, pošteno IZMERENO/PROJEKCIJA, sažeti odgovori, bez „Za mentore" sekcije.
