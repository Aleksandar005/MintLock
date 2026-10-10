// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "./Goldilocks.sol";

/// @title DeepComposer — DEEP kompoziciona provera, replika Winterfell DeepComposer.
/// @notice DEO 4/5 punog FRI+DEEP verifikatora. Dve ključne provere:
///   (A) OOD konzistentnost: eval constraint-a u z (iz OOD trace frame-a) ==
///       Σ_i z^(i·traceLen) · H_i(z)  (redukcija OOD constraint kolona). Ako ne == → reject.
///   (B) DEEP kombinacija po query poziciji x (ulaz u FRI, Deo 5):
///       trace:      T(x) = Σ_i[(T_i(x)−T_i(z))(x−zg) + (T_i(x)−T_i(zg))(x−z)]·cc_i / [(x−z)(x−zg)]
///       constraint: C(x) = Σ_i (H_i(x) − H_i(z))·cc_i / (x − z)
///       deep(x) = T(x) + C(x)
///   Sve u Fp2 (Goldilocks²). z = OOD tačka, zg = z·g (g = trace_domain_generator).
///
/// Test-vektori (deep_vectors) potvrđuju formule protiv Winterfell QuadExtension aritmetike.
library DeepComposer {
    using Goldilocks for Goldilocks.Fp2;

    /// @notice (A) OOD redukcija: Σ_i z^(i·traceLen) · Hcol_i(z).
    /// @param z OOD tačka (Fp2)
    /// @param traceLen dužina traga (N)
    /// @param hcols OOD evaluacije constraint kompozicionih kolona H_i(z)
    /// @return H(z) rekonstruisano iz kolona
    function reduceOodConstraints(
        Goldilocks.Fp2 memory z, uint64 traceLen, Goldilocks.Fp2[] memory hcols
    ) internal pure returns (Goldilocks.Fp2 memory) {
        Goldilocks.Fp2 memory acc = Goldilocks.Fp2(0, 0);
        // z^traceLen, pa stepenujemo kumulativno: z^(i·traceLen)
        Goldilocks.Fp2 memory zPowStep = Goldilocks.e_exp(z, traceLen); // z^traceLen
        Goldilocks.Fp2 memory zPow = Goldilocks.Fp2(1, 0);             // z^(0·traceLen)
        for (uint256 i = 0; i < hcols.length; i++) {
            acc = Goldilocks.e_add(acc, Goldilocks.e_mul(zPow, hcols[i]));
            zPow = Goldilocks.e_mul(zPow, zPowStep);
        }
        return acc;
    }

    /// @notice (A) OOD konzistentnost: proveri eval1 (constraint eval u z) == eval2 (redukcija).
    function checkOodConsistency(
        Goldilocks.Fp2 memory eval1,
        Goldilocks.Fp2 memory z, uint64 traceLen, Goldilocks.Fp2[] memory hcols
    ) internal pure returns (bool) {
        Goldilocks.Fp2 memory eval2 = reduceOodConstraints(z, traceLen, hcols);
        return Goldilocks.e_eq(eval1, eval2);
    }

    struct DeepInput {
        Goldilocks.Fp2 z;          // OOD tačka
        Goldilocks.Fp2 zg;         // z · g
        Goldilocks.Fp2[] ccTrace;  // DEEP koeficijenti za trace kolone
        Goldilocks.Fp2[] ccCon;    // DEEP koeficijenti za constraint kolone
        Goldilocks.Fp2[] tz;       // T_i(z)   (OOD trace, tekući red)
        Goldilocks.Fp2[] tzg;      // T_i(zg)  (OOD trace, sledeći red)
        Goldilocks.Fp2[] hz;       // H_i(z)   (OOD constraint evaluacije)
    }

    /// @notice (B) DEEP vrednost za jednu query poziciju.
    /// @param inp OOD podaci + koeficijenti
    /// @param x koordinata query pozicije (Fp2)
    /// @param traceRow otvorene trace vrednosti T_i(x) (bazne, prebacuju se u Fp2)
    /// @param conRow otvorene constraint evaluacije H_i(x) (Fp2)
    function composeAt(
        DeepInput memory inp,
        Goldilocks.Fp2 memory x,
        uint64[] memory traceRow,
        Goldilocks.Fp2[] memory conRow
    ) internal pure returns (Goldilocks.Fp2 memory) {
        // --- trace kompozicija ---
        Goldilocks.Fp2 memory t1 = Goldilocks.Fp2(0, 0);
        Goldilocks.Fp2 memory t2 = Goldilocks.Fp2(0, 0);
        for (uint256 i = 0; i < traceRow.length; i++) {
            Goldilocks.Fp2 memory val = Goldilocks.Fp2(traceRow[i] % Goldilocks.P, 0);
            // t1 += (val − T_i(z))·cc_i ; t2 += (val − T_i(zg))·cc_i
            t1 = Goldilocks.e_add(t1, Goldilocks.e_mul(Goldilocks.e_sub(val, inp.tz[i]), inp.ccTrace[i]));
            t2 = Goldilocks.e_add(t2, Goldilocks.e_mul(Goldilocks.e_sub(val, inp.tzg[i]), inp.ccTrace[i]));
        }
        Goldilocks.Fp2 memory t1den = Goldilocks.e_sub(x, inp.z);
        Goldilocks.Fp2 memory t2den = Goldilocks.e_sub(x, inp.zg);
        // num = t1·t2den + t2·t1den ; den = t1den·t2den
        Goldilocks.Fp2 memory tnum = Goldilocks.e_add(
            Goldilocks.e_mul(t1, t2den), Goldilocks.e_mul(t2, t1den));
        Goldilocks.Fp2 memory tden = Goldilocks.e_mul(t1den, t2den);
        Goldilocks.Fp2 memory tcomp = Goldilocks.e_mul(tnum, Goldilocks.e_inv(tden));

        // --- constraint kompozicija ---
        Goldilocks.Fp2 memory cnum = Goldilocks.Fp2(0, 0);
        for (uint256 i = 0; i < conRow.length; i++) {
            cnum = Goldilocks.e_add(cnum, Goldilocks.e_mul(
                Goldilocks.e_sub(conRow[i], inp.hz[i]), inp.ccCon[i]));
        }
        Goldilocks.Fp2 memory ccomp = Goldilocks.e_mul(cnum, Goldilocks.e_inv(
            Goldilocks.e_sub(x, inp.z)));

        // --- kombinacija ---
        return Goldilocks.e_add(tcomp, ccomp);
    }
}
