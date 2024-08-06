fn main() {
    let mut x = 42;
    let r = &mut x;
    *r = *r + 1;
    assert!(x == 43);
}
