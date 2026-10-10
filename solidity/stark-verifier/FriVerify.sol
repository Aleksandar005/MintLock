// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "./Goldilocks.sol";

/// @title FriVerify — FRI folding verifikacija, replika Winterfell FriVerifier (folding_factor=4).
/// @notice DEO 5/5 punog FRI+DEEP verifikatora. Zatvara pun verifier lanac.
///   Po sloju (Winterfell verify_generic, N=4):
///     1. layer_values (4 vrednosti po foldovanoj poziciji) — otvorene iz layer commitment-a;
///        konzistentnost: evaluations prethodnog sloja == query_values ovog sloja (Merkle, Deo 3).
///     2. x-koordinate reda: xe = g^fpos · offset ; xs[k] = xe · folding_root[k], k=0..3
///        (folding_root[k] = g^(domain_size/4 · k) — 4-ti koreni jedinice).
///     3. fold: interpoliraj (xs, ys) u row poly, evaluiraj u alpha. Ekvivalentno (i jeftinije)
///        Lagrange evaluaciji:  folded = Σ_k y_k · Π_{j≠k}(alpha−x_j)/(x_k−x_j).
///     4. sledeći sloj: domain_generator ^= 4, domain_size /= 4, max_deg /= 4.
///   Na kraju: remainder poly (Horner eval) mora dati poslednje evaluations na svim pozicijama.
///
/// Test-vektori (fri_vectors) potvrđuju da Lagrange fold == Winterfell polynom::interpolate+eval.
library FriVerify {
    uint256 internal constant FF = 4; // folding factor

    /// @notice Folding root-ovi: g^(domainSize/4 · k), k=0..3 (bazni, u Fp2 kao (r,0)).
    function foldingRoots(uint64 g, uint64 domainSize) internal pure returns (Goldilocks.Fp2[4] memory roots) {
        uint64 step = domainSize / uint64(FF);
        for (uint256 k = 0; k < FF; k++) {
            roots[k] = Goldilocks.Fp2(Goldilocks.exp(g, step * uint64(k)), 0);
        }
    }

    /// @notice x-koordinate reda za foldovanu poziciju: xs[k] = (g^fpos · offset) · root[k].
    function rowXCoords(
        uint64 g, uint64 offset, uint64 fpos, Goldilocks.Fp2[4] memory roots
    ) internal pure returns (Goldilocks.Fp2[4] memory xs) {
        uint64 xe = Goldilocks.mul(Goldilocks.exp(g, fpos), offset);
        Goldilocks.Fp2 memory xeE = Goldilocks.Fp2(xe, 0);
        for (uint256 k = 0; k < FF; k++) {
            xs[k] = Goldilocks.e_mul(xeE, roots[k]);
        }
    }

    /// @notice Jedan folding korak: Lagrange eval (xs, ys) u alpha.
    ///   folded = Σ_k y_k · Π_{j≠k}(alpha − x_j) / (x_k − x_j).
    ///   Ekvivalentno Winterfell interpolate_batch + eval, ali bez eksplicitnog polinoma.
    function foldStep(
        Goldilocks.Fp2[4] memory xs,
        Goldilocks.Fp2[4] memory ys,
        Goldilocks.Fp2 memory alpha
    ) internal pure returns (Goldilocks.Fp2 memory) {
        Goldilocks.Fp2 memory folded = Goldilocks.Fp2(0, 0);
        for (uint256 k = 0; k < FF; k++) {
            Goldilocks.Fp2 memory num = Goldilocks.Fp2(1, 0);
            Goldilocks.Fp2 memory den = Goldilocks.Fp2(1, 0);
            for (uint256 j = 0; j < FF; j++) {
                if (j == k) continue;
                num = Goldilocks.e_mul(num, Goldilocks.e_sub(alpha, xs[j]));
                den = Goldilocks.e_mul(den, Goldilocks.e_sub(xs[k], xs[j]));
            }
            Goldilocks.Fp2 memory term = Goldilocks.e_mul(ys[k], Goldilocks.e_mul(num, Goldilocks.e_inv(den)));
            folded = Goldilocks.e_add(folded, term);
        }
        return folded;
    }

    /// @notice Horner evaluacija remainder polinoma u tački x (Fp2 koeficijenti).
    ///   Winterfell: comp_eval = eval_horner(remainder, offset · g^position).
    function evalHorner(
        Goldilocks.Fp2[] memory coeffs, Goldilocks.Fp2 memory x
    ) internal pure returns (Goldilocks.Fp2 memory) {
        Goldilocks.Fp2 memory acc = Goldilocks.Fp2(0, 0);
        for (uint256 i = coeffs.length; i > 0; i--) {
            acc = Goldilocks.e_add(Goldilocks.e_mul(acc, x), coeffs[i - 1]);
        }
        return acc;
    }

    /// @notice Konzistentnost sloja: da li se foldovana vrednost poklapa sa vrednošću
    ///   sledećeg sloja na odgovarajućoj poziciji (evaluations == query_values, Deo 3 Merkle).
    function checkLayerConsistency(
        Goldilocks.Fp2 memory folded, Goldilocks.Fp2 memory nextLayerValue
    ) internal pure returns (bool) {
        return Goldilocks.e_eq(folded, nextLayerValue);
    }

    /// @notice Finalna remainder provera: za svaku preostalu poziciju,
    ///   eval_horner(remainder, offset · g^pos) == poslednje evaluations.
    function checkRemainder(
        Goldilocks.Fp2[] memory remainder,
        uint64 g, uint64 offset, uint64 pos,
        Goldilocks.Fp2 memory evaluation
    ) internal pure returns (bool) {
        uint64 x = Goldilocks.mul(offset, Goldilocks.exp(g, pos));
        Goldilocks.Fp2 memory comp = evalHorner(remainder, Goldilocks.Fp2(x, 0));
        return Goldilocks.e_eq(comp, evaluation);
    }
}
