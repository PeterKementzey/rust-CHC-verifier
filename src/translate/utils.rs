use crate::smtlib2::Expr::*;
use crate::smtlib2::Operation::*;
use crate::smtlib2::{HornClause, PredicateRef};

static mut QUERY_COUNT: i32 = 0;

unsafe fn get_new_query_name() -> String {
    QUERY_COUNT += 1;
    format!("q{}", QUERY_COUNT)
}

pub(crate) trait CHCSystem {
    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause;

    fn get_latest_query(&self) -> Option<PredicateRef>;
}

impl CHCSystem for Vec<HornClause> {
    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause {
        let prev_query = self.get_latest_query();
        let mut new_query = prev_query
            .as_ref()
            .map(|query| query.to_stripped_enum())
            .unwrap_or_else(|| App(Predicate("query".to_string()), Vec::new()));

        let new_query_name = unsafe { get_new_query_name() };
        if let App(Predicate(name), _) = &mut new_query {
            *name = new_query_name;
        }

        let body = prev_query
            .map(|query| vec![query.to_stripped_enum()])
            .unwrap_or_else(Vec::new);

        HornClause {
            head: new_query,
            body,
        }
    }

    fn get_latest_query(&self) -> Option<PredicateRef> {
        self.iter().rev().find_map(|clause| {
            if let App(Predicate(name), args) = &clause.head {
                for arg in args {
                    if let Var(_) = arg {
                    } else {
                        panic!("Latest CHC head contains a non-variable argument");
                    }
                }
                Some(PredicateRef::ref_to(name, args))
            } else {
                None
            }
        })
    }
}
