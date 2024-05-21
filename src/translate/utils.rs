use crate::smtlib2::Expr::*;
use crate::smtlib2::Operation::*;

static mut QUERY_COUNT: i32 = 0;

pub(crate) unsafe fn get_new_query_name() -> String {
    QUERY_COUNT += 1;
    format!("q{}", QUERY_COUNT)
}
