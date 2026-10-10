// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "./Goldilocks.sol";

/// @title Transcript — Fiat-Shamir RandomCoin, tačna replika Winterfell DefaultRandomCoin.
/// @notice DEO 2/5 punog FRI+DEEP verifikatora. Reprodukuje bit-za-bit:
///   - new(seed_elems):      seed = H(elements_as_bytes(seed_elems))
///   - reseed(digest):       seed = H(seed || digest)
///   - next():               counter++; H(seed || counter_LE8)
///   - draw() (Fp):          čitaj 8 LE bajtova iz next(); validan akko < p (canonical)
///   - drawExt() (Fp2):      dva uzastopna draw() (c0, c1)
///   - drawIntegers(k, dom): seed = H(seed || nonce_LE8); counter=0; (LE8 & (dom−1))
///
/// HASH: Winterfell koristi Blake3_256. EVM nema native Blake3, pa je hash apstrahovan
///   kroz `_hash(bytes)`. Priložena `Blake3` referenca (poseban fajl) ili — realnije za
///   produkciju — regenerisati dokaz sa keccak hasher-om (ista transcript LOGIKA, samo
///   `_hash = keccak256`). Validacija (transcript_vectors) potvrđuje da je SERIJALIZACIJA
///   tačna; izbor hash-a je nezavisan od nje.
///
/// Serijalizacija (potvrđeno protiv Winterfell-a):
///   merge_with_int(seed, v) = H(seed[32] || v.to_le_bytes()[8])
///   merge([a,b])            = H(a[32] || b[32])
///   hash_elements(e)        = H(concat(e_i.to_le_bytes()[8]))   // f64 canonical LE
abstract contract Transcript {
    uint64 internal constant P = 0xFFFFFFFF00000001;

    struct Coin {
        bytes32 seed;
        uint64  counter;
    }

    // ---- hash apstrakcija (Blake3 u produkciji; override u konkretnom verifieru) ----
    function _hash(bytes memory data) internal pure virtual returns (bytes32);

    // ---- konstrukcija ----
    /// @notice new(seed_elems): seed = H(LE8 concat elemenata).
    function coinNew(uint64[] memory seedElems) internal pure returns (Coin memory c) {
        bytes memory buf = new bytes(seedElems.length * 8);
        for (uint256 i = 0; i < seedElems.length; i++) {
            _putLE64(buf, i * 8, seedElems[i]);
        }
        c.seed = _hash(buf);
        c.counter = 0;
    }

    // ---- reseed ----
    /// @notice reseed(digest): seed = H(seed || digest); counter = 0.
    function coinReseed(Coin memory c, bytes32 digest) internal pure {
        c.seed = _hash(abi.encodePacked(c.seed, digest));
        c.counter = 0;
    }

    /// @notice reseed sa u64 (merge_with_int): seed = H(seed || v_LE8); counter = 0.
    function coinReseedInt(Coin memory c, uint64 v) internal pure {
        c.seed = _mergeWithInt(c.seed, v);
        c.counter = 0;
    }

    // ---- next (interno) ----
    function _next(Coin memory c) private pure returns (bytes32) {
        c.counter += 1;
        return _mergeWithInt(c.seed, c.counter);
    }

    function _mergeWithInt(bytes32 seed, uint64 v) private pure returns (bytes32) {
        bytes memory data = new bytes(40);
        assembly { mstore(add(data, 32), seed) }        // data[0..32] = seed
        _putLE64(data, 32, v);                           // data[32..40] = v LE
        return _hash(data);
    }

    // ---- draw (Fp) ----
    /// @notice Sledeći bazni element: čitaj 8 LE bajtova iz next(); validan akko < p.
    function coinDraw(Coin memory c) internal pure returns (uint64) {
        for (uint256 i = 0; i < 1000; i++) {
            bytes32 d = _next(c);
            uint64 v = _readLE64(d);
            if (v < P) return v;
        }
        revert("draw: 1000 pokusaja");
    }

    /// @notice Sledeći Fp2 element: dva uzastopna coinDraw (c0, c1).
    function coinDrawExt(Coin memory c) internal pure returns (Goldilocks.Fp2 memory) {
        uint64 a0 = coinDraw(c);
        uint64 a1 = coinDraw(c);
        return Goldilocks.Fp2(a0, a1);
    }

    // ---- draw_integers ----
    /// @notice k celih brojeva iz [0, domainSize) posle reseed-a nonce-om.
    ///   domainSize mora biti stepen dvojke. Vrednosti mogu biti duplirane (kao Winterfell).
    function coinDrawIntegers(
        Coin memory c, uint256 k, uint256 domainSize, uint64 nonce
    ) internal pure returns (uint256[] memory) {
        require(_isPow2(domainSize), "domain nije stepen 2");
        require(k < domainSize, "k >= domain");
        c.seed = _mergeWithInt(c.seed, nonce);
        c.counter = 0;
        uint64 mask = uint64(domainSize - 1);
        uint256[] memory out = new uint256[](k);
        uint256 got = 0;
        for (uint256 i = 0; i < 1000 && got < k; i++) {
            bytes32 d = _next(c);
            uint64 v = _readLE64(d) & mask;
            out[got++] = uint256(v);
        }
        require(got == k, "drawIntegers: nedovoljno");
        return out;
    }

    // ---- helpers: little-endian 64-bit ----
    function _putLE64(bytes memory buf, uint256 off, uint64 v) private pure {
        for (uint256 j = 0; j < 8; j++) {
            buf[off + j] = bytes1(uint8(v >> (8 * j)));
        }
    }

    /// @notice Čita prvih 8 bajtova digest-a kao little-endian u64.
    function _readLE64(bytes32 d) private pure returns (uint64) {
        uint64 v = 0;
        for (uint256 j = 0; j < 8; j++) {
            v |= uint64(uint8(d[j])) << (8 * j);
        }
        return v;
    }

    function _isPow2(uint256 x) private pure returns (bool) {
        return x != 0 && (x & (x - 1)) == 0;
    }
}
