fn main() {
    let mut x = 42;
    let mut y = &mut x;
    let mut a = 0;
    let b = &mut a;
    *y = *y + 1;
    *b = 4;
    y = b;
    *y = *y + 1;
    assert!(x == 43);
    assert!(a == 5);
}
