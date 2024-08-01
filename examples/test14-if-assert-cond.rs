fn main() {
    let mut x = 42;
    let y = &mut x;
    *y = 51;
    if *y > 50 {
        assert!(x > 50);
    } else {
        assert!(x <= 50);
    }
}
