fn main() {
    let x = 42;
    let mut y = &x;
    // bug here, b is translated as a variable instead of a reference
    let b = y;
    assert!(*b == 42);
    y = b;
    y = b;
    assert!(*y == 42);
}
