fn main() {
    let a = 42;
    let b = 4;
    assert!(a == 42 && b == 4);
    assert!(a == 42 || b == 5);
    assert!(!(a == 43));
}
