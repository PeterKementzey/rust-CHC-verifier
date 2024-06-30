fn main() {
    let x = 42;
    let mut y = &x;
    let a = 0;
    let b = &a;
    assert!(*y == 42);
    y = b;
    assert!(x == 42);
    assert!(*y == 0);
    assert!(*b == 0);
}
