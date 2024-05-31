fn main() {
    let mut x = 42;
    let y = &mut x;
    // *y = *y + 1;
    // end of borrow
    assert!(x == 43);
}
