fn main() {
    let mut x = 1;
    let mut y = 2;
    let mut unused = 0;
    let mut r = &mut unused;
    if x > rand::random() {
        r = &mut x;
    } else {
        r = &mut y;
    }
    *r = 3;
    assert!((x == 3 && y == 2) || (x == 1 && y == 3));
}
