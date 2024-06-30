use crate::smtlib2;
use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::Operation::Predicate;
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
                    #[allow(clippy::manual_assert)]
                    if !matches!(arg, Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_)) {
                        panic!("Latest CHC head contains a non-variable argument: {arg}");
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
    pub(super) fn insert_head_query_param(&mut self, new_query_param: smtlib2::Expr) {
        if let App(Predicate(_), query_params) = &mut self.head {
            query_params.push(new_query_param);
        } else {
            panic!("Cannot insert if head of CHC is not a predicate");
        }
    }

    pub(super) fn replace_head_query_param(
        &mut self,
        old_query_param: &smtlib2::Expr,
        new_query_param: smtlib2::Expr,
    ) {
        let query_params = self.get_mut_head_query_params();
        match query_params.iter().position(|var| *var == *old_query_param) {
            Some(old_var_index) => query_params[old_var_index] = new_query_param,
            _ => panic!("Query parameter not found in head of CHC"),
        }
    }

    pub(super) fn head_contains(&self, var: &smtlib2::Expr) -> bool {
        if let App(Predicate(_), query_params) = &self.head {
            query_params.contains(var)
        } else {
            panic!("Cannot check if head of CHC is not a predicate");
        }
    }

    pub(super) fn get_mut_head_query_params(&mut self) -> &mut Vec<smtlib2::Expr> {
        if let App(Predicate(_), query_params) = &mut self.head {
            query_params
        } else {
            panic!("Cannot get query parameters if head of CHC is not a predicate");
        }
    }
}

impl PredicateRef<'_> {
    pub(super) fn to_expr_without_trailing_apostrophes(&self) -> smtlib2::Expr {
        let (name, _) = self.get_name_and_args();
        let stripped_args = self.get_stripped_query_params();

        App(Predicate(name.clone()), stripped_args)
    }

    pub(super) fn get_stripped_query_params(&self) -> Vec<smtlib2::Expr> {
        fn strip_trailing_apostrophes(name: &str) -> String {
            let mut new_name = name.to_string();
            while new_name.ends_with('\'') {
                new_name.pop();
            }
            new_name
        }

        let (_, args) = self.get_name_and_args();

        let stripped_args: Vec<smtlib2::Expr> = args
            .iter()
            .map(|arg| match arg {
                Var(name) => Var(strip_trailing_apostrophes(name)),
                ReferenceCurrVal(name) => ReferenceCurrVal(strip_trailing_apostrophes(name)),
                ReferenceFinalVal(name) => ReferenceFinalVal(strip_trailing_apostrophes(name)),
                _ => panic!("Non-variable argument in predicate reference"),
            })
            .collect();

        stripped_args
    }
}

pub struct AliasGroups {
    groups: Vec<AliasGroup>,
}

impl AliasGroups {
    pub fn new() -> Self {
        AliasGroups { groups: Vec::new() }
    }

    pub(super) fn find_curr_name(&self, name: &String) -> Option<&String> {
        self.groups
            .iter()
            .find(|group| group.contains(name))
            .map(|group| &group.curr_name)
    }

    /// If no group contains either alias, then alias1 will be the current name of a new group
    pub(super) fn add_alias(&mut self, alias1: String, alias2: String) -> &String {
        let index = self
            .groups
            .iter()
            .position(|group| group.contains(&alias1) || group.contains(&alias2));
        if let Some(index) = index {
            let group = &mut self.groups[index];
            group.insert_alias(alias1);
            group.insert_alias(alias2);
            &group.curr_name
        } else {
            self.groups.push(AliasGroup {
                curr_name: alias1,
                aliases: vec![alias2],
            });
            &self.groups.last().unwrap().curr_name
        }
    }

    pub(super) fn shift_curr_name_in_group(&mut self, curr_name: &String) {
        let group = self
            .groups
            .iter_mut()
            .find(|group| group.curr_name == *curr_name)
            .expect("Name not found in any group");
        std::mem::swap(
            &mut group.curr_name,
            group.aliases.last_mut().expect("No aliases to shift"),
        );
    }

    pub(super) fn drop_alias(&mut self, alias: &String) {
        let index = self.groups.iter().position(|group| group.contains(alias));
        match index {
            Some(index) => {
                let group = &mut self.groups[index];
                assert_ne!(
                    group.curr_name, *alias,
                    "Cannot drop current name of alias group"
                );
                group.aliases.retain(|name| name != alias);
                if group.aliases.is_empty() {
                    self.groups.remove(index);
                }
            }
            None => panic!("Alias not found in any group"),
        }
    }
}

struct AliasGroup {
    curr_name: String,
    aliases: Vec<String>,
}

impl AliasGroup {
    fn contains(&self, name: &String) -> bool {
        self.curr_name == *name || self.aliases.contains(name)
    }

    fn insert_alias(&mut self, alias: String) {
        if !self.contains(&alias) {
            self.aliases.push(alias);
        }
    }
}
