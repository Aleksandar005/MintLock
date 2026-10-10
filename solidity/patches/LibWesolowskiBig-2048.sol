// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {LibBigInt as B} from "./LibBigInt.sol";
import {LibClassGroupBig as CG} from "./LibClassGroupBig.sol";

/// @title On-chain Wesolowski verifikacija nad klasnom grupom (do 2048-bit).
/// @dev Kanonska serijalizacija forme (mora biti IDENTICNA python strani,
///      videti gen_wesolowski_fixture.py): a(PAD_BYTES BE) || sign(b)(1B) ||
///      |b|(PAD_BYTES BE) || c(PAD_BYTES BE). Seed = sha256(ser(u)||ser(w)||
///      T(32B)||D(PAD_BYTES BE)); kandidat l = sha256(seed||counter) >> 176 |
///      (1<<79) | 1  — SIRINA IZAZOVA l JE NEZAVISNA od sirine D (ostaje ~80-bit).
///
///      PAD_WORDS je jedini parametar sirine: 8 reci = 256 bajtova pokriva
///      2048-bit diskriminantu (redukovane forme mogu imati koeficijent c ~ |D|
///      bita kad je a mali, i sam D je 8 limbova). Za pravu sigurnost
///      (Dobson–Galbraith ~6656-bit) povecati PAD_WORDS na 26 (i uskladiti
///      python pad) — nikakva druga promena nije potrebna.
library LibWesolowskiBig {
    uint256 internal constant PAD_WORDS = 8;          // 8 * 32 = 256 bajtova
    uint256 internal constant PAD_BYTES = PAD_WORDS * 32;

    /// @dev big-endian pad na PAD_BYTES; L[0] je najmanje znacajna rec.
    function _pad(B.Int memory x) private pure returns (bytes memory out) {
        uint256[] memory L = x.limbs;
        uint256 n = L.length;
        require(n <= PAD_WORDS, "form too wide");
        out = new bytes(PAD_BYTES);
        // rec L[i] ide u blok (PAD_WORDS-1-i); visi blokovi ostaju 0
        for (uint256 i = 0; i < n; i++) {
            uint256 word = L[i];
            uint256 base = (PAD_WORDS - 1 - i) * 32;
            assembly {
                mstore(add(add(out, 0x20), base), word)
            }
        }
    }

    function _ser(CG.Form memory f) private pure returns (bytes memory) {
        return abi.encodePacked(
            _pad(f.a),
            uint8(f.b.neg ? 1 : 0),
            _pad(f.b),
            _pad(f.c)
        );
    }

    function fiatShamirPrime(
        CG.Form memory u, CG.Form memory w, uint256 T, B.Int memory D
    ) internal pure returns (uint256) {
        bytes32 seed = sha256(
            abi.encodePacked(_ser(u), _ser(w), T, _pad(D))
        );
        for (uint256 counter = 0;; counter++) {
            uint256 cand = uint256(sha256(abi.encodePacked(seed, counter))) >> 176;
            cand |= (1 << 79) | 1;               // ~80-bit izazov, nezavisno od |D|
            if (millerRabin(cand)) return cand;
        }
    }

    /// @notice proverava pi^l * u^r == w  (l Fiat-Shamir prost, r = 2^T mod l)
    function verify(
        CG.Form memory u, CG.Form memory w, CG.Form memory pi,
        uint256 T, B.Int memory D
    ) internal pure returns (bool) {
        uint256 l = fiatShamirPrime(u, w, T, D);
        uint256 r = powmod(2, T, l);
        return CG.eq(CG.shamir(pi, l, u, r, D), CG.reduce(w));
    }

    /// @dev deterministicki Miller-Rabin, 12 baza — dovoljno za 80-bit kandidate
    function millerRabin(uint256 n) internal pure returns (bool) {
        uint256[12] memory bases =
            [uint256(2), 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
        for (uint256 i = 0; i < 12; i++) {
            if (n % bases[i] == 0) return n == bases[i];
        }
        uint256 d = n - 1;
        uint256 s = 0;
        while (d & 1 == 0) { d >>= 1; s++; }
        for (uint256 i = 0; i < 12; i++) {
            uint256 x = powmod(bases[i], d, n);
            if (x == 1 || x == n - 1) continue;
            bool passed = false;
            for (uint256 j = 0; j + 1 < s; j++) {
                x = mulmod(x, x, n);
                if (x == n - 1) { passed = true; break; }
            }
            if (!passed) return false;
        }
        return true;
    }

    function powmod(uint256 base, uint256 e, uint256 m) internal pure returns (uint256 r) {
        r = 1 % m;
        base %= m;
        while (e > 0) {
            if (e & 1 == 1) r = mulmod(r, base, m);
            base = mulmod(base, base, m);
            e >>= 1;
        }
    }
}
