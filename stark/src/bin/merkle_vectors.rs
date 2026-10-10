// Emituje Winterfell Merkle vektore: listovi (iz redova field elemenata), koren, putevi.
use winterfell::crypto::{hashers::Blake3_256, Hasher, Digest, ElementHasher, MerkleTree};
use winterfell::math::fields::f64::BaseElement;
type H = Blake3_256<BaseElement>;
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }
fn main() {
    // 8 listova, svaki red od 3 field elementa -> leaf = hash_elements(row)
    let rows: Vec<[BaseElement;3]> = (0..8u64).map(|i|
        [BaseElement::new(i*100+1), BaseElement::new(i*100+2), BaseElement::new(i*100+3)]).collect();
    let leaves: Vec<_> = rows.iter().map(|r| H::hash_elements(r)).collect();
    let tree = MerkleTree::<H>::new(leaves.clone()).unwrap();
    println!("ROOT {}", hex(&tree.root().as_bytes()));
    for (i,r) in rows.iter().enumerate() {
        // leaf digest
        let ld = H::hash_elements(r);
        println!("LEAF{} row={},{},{} digest={}", i,
            {use winterfell::math::StarkField; r[0].as_int()},
            {use winterfell::math::StarkField; r[1].as_int()},
            {use winterfell::math::StarkField; r[2].as_int()},
            hex(&ld.as_bytes()));
    }
    // putevi za par indeksa
    for &idx in &[0usize, 3, 5, 7] {
        let path = tree.prove(idx).unwrap();
        let ph: Vec<String> = path.iter().map(|d| hex(&d.as_bytes())).collect();
        println!("PATH{} {}", idx, ph.join(","));
    }
}
