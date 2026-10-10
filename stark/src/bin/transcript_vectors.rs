// Emituje Winterfell RandomCoin (Blake3_256) transcript vektore za validaciju Solidity Transcript-a.
use winterfell::crypto::{hashers::Blake3_256, DefaultRandomCoin, RandomCoin, Hasher, Digest, ElementHasher};
use winterfell::math::fields::f64::BaseElement;
type H = Blake3_256<BaseElement>;
type RC = DefaultRandomCoin<H>;
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }
fn main() {
    // seed elementi
    let seed_elems = [BaseElement::new(11), BaseElement::new(22), BaseElement::new(33)];
    let mut coin = RC::new(&seed_elems);
    // init seed digest
    let init = H::hash_elements(&seed_elems);
    println!("SEED_ELEMS 11,22,33");
    println!("INIT_SEED {}", hex(&init.as_bytes()));
    // draw 3 base elements
    for i in 0..3 {
        let e: BaseElement = coin.draw().unwrap();
        use winterfell::math::StarkField;
        println!("DRAW{} {}", i, e.as_int());
    }
    // reseed with a digest (hash of some bytes)
    let d = H::hash(&[1,2,3,4,5]);
    println!("RESEED_DIGEST {}", hex(&d.as_bytes()));
    coin.reseed(d);
    for i in 0..2 {
        let e: BaseElement = coin.draw().unwrap();
        use winterfell::math::StarkField;
        println!("DRAW_AFTER_RESEED{} {}", i, e.as_int());
    }
    // draw_integers
    let vals = coin.draw_integers(8, 65536, 0).unwrap();
    println!("INTEGERS {}", vals.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","));
}
