fn main() {
    let mut x = 42;
    {
        // don't need `let mut y` as the reference stays the same
        let y = &mut x;
        *y = *y + 1;
    }
    assert!(x == 43);
}
