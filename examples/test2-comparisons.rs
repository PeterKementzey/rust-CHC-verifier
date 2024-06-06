fn main() {
    let x = 42;
    let y = 4;
    assert!(x == x);
    assert!(y != x);
    assert!(y < x);
    assert!(y <= x);
    assert!(x > y);
    assert!(x >= y);
}
