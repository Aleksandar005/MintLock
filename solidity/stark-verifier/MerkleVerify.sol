// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @title MerkleVerify — verifikacija trace/constraint commitmenata, replika Winterfell MerkleTree.
/// @notice DEO 3/5 punog FRI+DEEP verifikatora. Verifikuje da otvorene query vrednosti
///   (redovi field elemenata) leže pod objavljenim Merkle korenom.
///
/// Winterfell layout (potvrđeno test-vektorima protiv MerkleTree::verify):
///   - LIST:  leaf_digest = H(elements_as_bytes(row))  = Blake3(concat LE8 elemenata reda)
///   - ČVOR:  merge(l, r) = H(l[32] || r[32])
///   - PUT:   proof[0..2] = (leaf, sibling); r = index&1; v = merge(proof[r], proof[1−r]);
///            zatim index = (index + 2^(len−1)) >> 1; za svaki proof[k>=2]:
///               v = (index&1==0) ? merge(v, p) : merge(p, v); index >>= 1;
///            validno akko v == root.
///
/// HASH: kao Deo 2 — Winterfell koristi Blake3; hash je apstrahovan `_hash`. Produkcija
///   koristi Blake3-u-Solidity ili keccak-varijantu dokaza. Test-vektori potvrđuju layout.
abstract contract MerkleVerify {
    uint64 internal constant PP = 0xFFFFFFFF00000001;

    function _hashBytes(bytes memory data) internal pure virtual returns (bytes32);

    /// @notice Leaf digest iz reda field elemenata: Blake3(concat LE8).
    function hashLeaf(uint64[] memory row) internal pure returns (bytes32) {
        bytes memory buf = new bytes(row.length * 8);
        for (uint256 i = 0; i < row.length; i++) {
            uint64 v = row[i] % PP;
            for (uint256 j = 0; j < 8; j++) {
                buf[i * 8 + j] = bytes1(uint8(v >> (8 * j)));
            }
        }
        return _hashBytes(buf);
    }

    /// @notice merge dva digest-a: H(l || r).
    function _merge(bytes32 l, bytes32 r) internal pure returns (bytes32) {
        return _hashBytes(abi.encodePacked(l, r));
    }

    /// @notice Verifikuje Winterfell Merkle put.
    /// @param root objavljeni koren (commitment)
    /// @param index pozicija lista (query pozicija)
    /// @param proof put: proof[0]=leaf, proof[1]=sibling, proof[2..]=čvorovi ka korenu
    /// @return true akko put razrešava do root
    function verifyMerkle(
        bytes32 root, uint256 index, bytes32[] memory proof
    ) internal pure returns (bool) {
        require(proof.length >= 2, "put prekratak");
        uint256 r = index & 1;
        bytes32 v = _merge(proof[r], proof[1 - r]);
        // re-baziraj index kao Winterfell: (index + 2^(len−1)) >> 1
        uint256 idx = (index + (1 << (proof.length - 1))) >> 1;
        for (uint256 k = 2; k < proof.length; k++) {
            if (idx & 1 == 0) {
                v = _merge(v, proof[k]);
            } else {
                v = _merge(proof[k], v);
            }
            idx >>= 1;
        }
        return v == root;
    }

    /// @notice Kombinovano: verifikuje da RED (query vrednosti) leži pod korenom.
    ///   proof[0] MORA biti hashLeaf(row) (list); ovde to i proveravamo.
    /// @param root Merkle koren
    /// @param index query pozicija
    /// @param row otvorene vrednosti reda (trace/constraint evaluacije na x_index)
    /// @param proof Merkle put (proof[0]=leaf digest, proof[1]=sibling, ...)
    function verifyOpening(
        bytes32 root, uint256 index, uint64[] memory row, bytes32[] memory proof
    ) internal pure returns (bool) {
        // list rekonstruisan iz vrednosti mora se poklopiti sa proof[0]
        bytes32 leaf = hashLeaf(row);
        if (leaf != proof[0]) return false;
        return verifyMerkle(root, index, proof);
    }
}
