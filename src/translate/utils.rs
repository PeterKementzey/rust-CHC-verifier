use crate::smtlib2::*;
use crate::smtlib2::Expr::*;
use crate::smtlib2::Operation::*;

pub(crate) fn get_latest_query(
    #[allow(non_snake_case)] CHCs: &Vec<HornClause>,
) -> Option<PredicateRef> {
    CHCs.last().map({
        |clause| {
            if let App(Predicate(name), args) = &clause.head {
                for arg in args {
                    if let Var(_) = arg {
                    } else {
                        panic!("Latest CHC head contains a non-variable argument");
                    }
                }
                PredicateRef { name, args }
            } else {
                panic!("Latest CHC head is not a predicate")
            }
        }
    })
}

static mut QUERY_COUNT: i32 = 0;
pub(crate) unsafe fn get_new_query_name() -> String {
    QUERY_COUNT += 1;
    format!("q{}", QUERY_COUNT)
}
