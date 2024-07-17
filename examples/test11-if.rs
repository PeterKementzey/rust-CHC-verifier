fn main() {
    let mut x = 42;
    let y = &mut x;
    let z = 42;
    if *y == z {
        let a = 3;
        x = 1;
    } else {
        x = z;
        x = 2;
    }
    assert!(x == 1);
    assert!(x != 2);
}
