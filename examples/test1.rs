fn main() {
    let hi = 10;
    let z = 0;
    let mut x = 42;
    x = x + 1 + z;
    assert!(x == 43);
    let y = x * 2;
    assert!(y == 86);
}
