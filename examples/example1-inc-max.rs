fn main() {
    let mut unused = 0; // We do not support uninitialized variables, so the reference needs to be initialized

    let mut a = 4;
    let mut b = 5;
    let r_a = &mut a;
    let r_b = &mut b;
    let mut r_max = &mut unused;
    if *r_a > *r_b {
        r_max = r_a;
    } else {
        r_max = r_b;
    }
    *r_max = *r_max + 1;
    assert!(a != b);
}
