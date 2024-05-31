use crate::smtlib2;
use crate::smtlib2::Expr::*;
use crate::smtlib2::Operation::*;
use crate::smtlib2::{HornClause, PredicateRef};

static mut QUERY_COUNT: i32 = 0;

unsafe fn get_new_query_name() -> String {
    QUERY_COUNT += 1;
    format!("q{}", QUERY_COUNT)
}

pub(super) trait CHCSystem {
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
                    if !matches!(arg, Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_)) {
                        panic!("Latest CHC head contains a non-variable argument: {}", arg);
                    }
                }
                Some(PredicateRef::ref_to(name, args))
            } else {
                None
            }
        })
    }
}

impl HornClause {
    pub(crate) fn insert_head_query_param(&mut self, new_query_param: smtlib2::Expr) {
        if let App(Predicate(_), query_params) = &mut self.head {
            query_params.push(new_query_param);
        } else {
            panic!("Cannot insert if head of CHC is not a predicate");
        }
    }

    pub(crate) fn replace_head_query_param(
        &mut self,
        old_query_param: &smtlib2::Expr,
        new_query_param: smtlib2::Expr,
    ) {
        if let App(Predicate(_), query_params) = &mut self.head {
            match query_params.iter().position(|var| *var == *old_query_param) {
                Some(old_var_index) => query_params[old_var_index] = new_query_param,
                _ => panic!("Query parameter not found in latest query"),
            }
        } else {
            panic!("Cannot replace if head of CHC is not a predicate");
        }
    }

    pub(crate) fn head_contains(&self, var: &smtlib2::Expr) -> bool {
        if let App(Predicate(_), query_params) = &self.head {
            query_params.contains(var)
        } else {
            panic!("Cannot check if head of CHC is not a predicate");
        }
    }
}
