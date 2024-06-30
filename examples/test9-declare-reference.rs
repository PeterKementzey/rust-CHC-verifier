fn main() {
    let x = 42;
    let mut y = &x;
    let b = y;
    assert!(*b == 42);
    y = b;
    y = b;
    assert!(*y == 42);
}
