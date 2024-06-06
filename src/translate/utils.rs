use crate::smtlib2;
use crate::smtlib2::Expr::*;
use crate::smtlib2::Operation::*;
use crate::smtlib2::{HornClause, PredicateRef};

fn get_new_query_name() -> String {
    // Need to use atomic for static variable because Rust deems mutable statics unsafe due to potential parallelism
    use std::sync::atomic::{AtomicU32, Ordering};
    static QUERY_COUNT: AtomicU32 = AtomicU32::new(1);
    format!("q{}", QUERY_COUNT.fetch_add(1, Ordering::Relaxed))
}

pub(super) trait CHCSystem {
    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause;

    fn get_latest_query(&self) -> Option<PredicateRef>;
}

impl CHCSystem for Vec<HornClause> {
    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause {
        let prev_query = self
            .get_latest_query()
            .map(|query| query.to_expr_without_trailing_apostrophes());

        let new_query = match &prev_query {
            Some(prev_query) => {
                let mut new_query = prev_query.clone();
                if let App(Predicate(name), _) = &mut new_query {
                    *name = get_new_query_name();
                }
                new_query
            }
            None => App(Predicate(get_new_query_name()), Vec::new()),
        };

        let body = match prev_query {
            Some(query) => vec![query],
            None => Vec::new(),
        };

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
                Some(PredicateRef::from(name, args))
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
                _ => panic!("Query parameter not found in head of CHC"),
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

    pub(crate) fn get_mut_head_query_params(&mut self) -> &mut Vec<smtlib2::Expr> {
        if let App(Predicate(_), query_params) = &mut self.head {
            query_params
        } else {
            panic!("Cannot get query parameters if head of CHC is not a predicate");
        }
    }
}

impl PredicateRef<'_> {
    pub(crate) fn to_expr_without_trailing_apostrophes(&self) -> smtlib2::Expr {
        fn strip_trailing_apostrophes(name: &String) -> String {
            let mut new_name = name.clone();
            while new_name.ends_with('\'') {
                new_name.pop();
            }
            new_name
        }

        let (name, args) = self.get_name_and_args();

        let stripped_args: Vec<smtlib2::Expr> = args
            .iter()
            .map(|arg| match arg {
                Var(name) => Var(strip_trailing_apostrophes(&name)),
                ReferenceCurrVal(name) => ReferenceCurrVal(strip_trailing_apostrophes(&name)),
                ReferenceFinalVal(name) => ReferenceFinalVal(strip_trailing_apostrophes(&name)),
                _ => panic!("Non-variable argument in predicate reference"),
            })
            .collect();

        App(Predicate(name.clone()), stripped_args)
    }
}
