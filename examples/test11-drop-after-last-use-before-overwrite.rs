fn main() {
    let mut a = 4;
    let mut b = 0;
    let mut r_a = &mut a;

    *r_a = 3;
    assert!(a == 3);

    r_a = &mut b;

    assert!(*r_a == 0);
}
