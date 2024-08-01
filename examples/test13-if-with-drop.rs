fn main() {
    let mut x = 0;
    let y = &mut x;
    *y = 2;
    if *y == 2 {
        *y = 1;
        assert!(x == 1); // testing if final value has been assigned
    } else {
        x = 2;
    }
    assert!(x == 1);
    assert!(x != 2);
}
