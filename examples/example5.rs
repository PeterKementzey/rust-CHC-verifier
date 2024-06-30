fn main() {
    let x = 42;
    let mut y = &x;
    let a = 0;
    assert!(*y == 42);
    y = &a;
    assert!(x == 42);
    assert!(*y == 0);
}
