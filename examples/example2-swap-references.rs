fn main() {
    let mut a = 1;
    let mut b = 2;
    let mut r_a = &mut a;
    let mut r_b = &mut b;
    let temp = r_a;
    r_a = r_b;
    r_b = temp;
    assert!(*r_a == 2);
    assert!(*r_b == 1);
}
