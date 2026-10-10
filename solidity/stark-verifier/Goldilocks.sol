// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @title Goldilocks — polje-aritmetika za on-chain STARK verifikaciju
/// @notice Bazno polje Fp, p = 2^64 − 2^32 + 1 (Goldilocks), i kvadratna ekstenzija
///         Fp2 = Fp[x]/(x² + 2)  (x² = −2), tačno kao Winterfell 0.8.x ExtensibleField<2>.
///         DEO 1/5 punog FRI+DEEP verifikatora. Sve dalje (transcript, Merkle, DEEP, FRI)
///         gradi se nad ovom aritmetikom.
///
/// Napomena o ispravnosti: p < 2^64, pa `mulmod(a, b, p)` u Solidity daje tačan rezultat
///         (mulmod radi punu 512-bit međuvrednost pre mod). Ne treba ručni Montgomery.
library Goldilocks {
    uint64 internal constant P = 0xFFFFFFFF00000001; // 2^64 − 2^32 + 1
    // p − 2 (za inverz preko Fermat: a^(p−2))
    uint64 internal constant P_MINUS_2 = 0xFFFFFFFEFFFFFFFF;

    // ============================ BAZNO POLJE Fp ============================

    function add(uint64 a, uint64 b) internal pure returns (uint64) {
        return uint64(addmod(a, b, P));
    }

    function sub(uint64 a, uint64 b) internal pure returns (uint64) {
        return uint64(addmod(a, P - b, P)); // b < P garantovano za reducirane ulaze
    }

    function mul(uint64 a, uint64 b) internal pure returns (uint64) {
        return uint64(mulmod(a, b, P));
    }

    function neg(uint64 a) internal pure returns (uint64) {
        return a == 0 ? 0 : P - a;
    }

    function dbl(uint64 a) internal pure returns (uint64) {
        return uint64(addmod(a, a, P));
    }

    /// @notice a^e binarnim stepenovanjem.
    function exp(uint64 a, uint64 e) internal pure returns (uint64) {
        uint64 r = 1;
        uint64 base = uint64(a % P);
        while (e != 0) {
            if (e & 1 == 1) r = uint64(mulmod(r, base, P));
            base = uint64(mulmod(base, base, P));
            e >>= 1;
        }
        return r;
    }

    /// @notice Inverz preko Fermat: a^(p−2). Revert ako a == 0.
    function inv(uint64 a) internal pure returns (uint64) {
        require(a % P != 0, "inv(0)");
        return exp(a, P_MINUS_2);
    }

    /// @notice Reducira proizvoljan uint256 (npr. iz keccak) u Fp.
    function fromUint(uint256 x) internal pure returns (uint64) {
        return uint64(x % P);
    }

    // ============================ EKSTENZIJA Fp2 (x² = x − 2) ============================
    // Ireducibilni polinom: x² − x + 2  (φ² = φ − 2), tačno kao Winterfell f64.
    // NAPOMENA: NIJE x²+2 — jer je −2 kvadratni ostatak mod p, pa x²+2 nije ireducibilan.
    // Element: c0 + c1·φ. Konjugat (frobenius): (c0 + c1) − c1·φ  ->  (c0+c1, −c1).
    // Element: c0 + c1·φ. Predstavljen kao par (c0, c1).

    struct Fp2 { uint64 c0; uint64 c1; }

    function e_from(uint64 c0, uint64 c1) internal pure returns (Fp2 memory) {
        return Fp2(c0, c1);
    }

    function e_add(Fp2 memory a, Fp2 memory b) internal pure returns (Fp2 memory) {
        return Fp2(add(a.c0, b.c0), add(a.c1, b.c1));
    }

    function e_sub(Fp2 memory a, Fp2 memory b) internal pure returns (Fp2 memory) {
        return Fp2(sub(a.c0, b.c0), sub(a.c1, b.c1));
    }

    function e_neg(Fp2 memory a) internal pure returns (Fp2 memory) {
        return Fp2(neg(a.c0), neg(a.c1));
    }

    /// @notice Množenje u Fp2 sa φ² = φ − 2 (Winterfell zakon, 3 bazna množenja):
    ///   real = a0·b0 − 2·(a1·b1)
    ///   imag = (a0 + a1)·(b0 + b1) − a0·b0
    /// (imag = a0b1 + a1b0 + a1b1, jer φ² doprinosi +a1b1 u φ-koeficijent)
    function e_mul(Fp2 memory a, Fp2 memory b) internal pure returns (Fp2 memory) {
        uint64 a0b0 = mul(a.c0, b.c0);
        uint64 a1b1 = mul(a.c1, b.c1);
        uint64 real = sub(a0b0, dbl(a1b1));
        uint64 imag = sub(mul(add(a.c0, a.c1), add(b.c0, b.c1)), a0b0);
        return Fp2(real, imag);
    }

    /// @notice Množenje Fp2 elementa baznim skalarom.
    function e_mulBase(Fp2 memory a, uint64 s) internal pure returns (Fp2 memory) {
        return Fp2(mul(a.c0, s), mul(a.c1, s));
    }

    /// @notice Kvadriranje: out0 = a0² − 2a1², out1 = 2a0a1 + a1² (Winterfell).
    function e_square(Fp2 memory a) internal pure returns (Fp2 memory) {
        uint64 a1sq = mul(a.c1, a.c1);
        uint64 out0 = sub(mul(a.c0, a.c0), dbl(a1sq));
        uint64 out1 = add(dbl(mul(a.c0, a.c1)), a1sq);
        return Fp2(out0, out1);
    }

    /// @notice Frobenius / konjugat: (c0 + c1, −c1).
    function e_conj(Fp2 memory a) internal pure returns (Fp2 memory) {
        return Fp2(add(a.c0, a.c1), neg(a.c1));
    }

    /// @notice Norma N(c0 + c1·φ) = c0² + c0·c1 + 2·c1²  (= a · conj(a), bazna vrednost).
    function e_norm(Fp2 memory a) internal pure returns (uint64) {
        return add(add(mul(a.c0, a.c0), mul(a.c0, a.c1)), dbl(mul(a.c1, a.c1)));
    }

    /// @notice Inverz u Fp2:  conj(a) / N(a).  Revert ako je element 0.
    function e_inv(Fp2 memory a) internal pure returns (Fp2 memory) {
        uint64 n = e_norm(a);
        require(n != 0, "e_inv(0)");
        uint64 ninv = inv(n);
        Fp2 memory c = e_conj(a);
        return Fp2(mul(c.c0, ninv), mul(c.c1, ninv));
    }

    function e_exp(Fp2 memory a, uint64 e) internal pure returns (Fp2 memory) {
        Fp2 memory r = Fp2(1, 0);
        Fp2 memory base = a;
        while (e != 0) {
            if (e & 1 == 1) r = e_mul(r, base);
            base = e_square(base);
            e >>= 1;
        }
        return r;
    }

    function e_eq(Fp2 memory a, Fp2 memory b) internal pure returns (bool) {
        return a.c0 == b.c0 && a.c1 == b.c1;
    }
}
