use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};

use crate::smtlib2::Expr::{App, Var, Const, ConstTrue};
use crate::smtlib2::Operation::Predicate;
use crate::translate::utils;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    Var(String),
    Const(i32),
    ConstTrue,
    App(Operation, Vec<Expr>),
}

impl Expr {
    pub fn var<S: Into<String>>(name: S) -> Self {
        Var(name.into())
    }

    fn extract_predicates<'a>(&'a self, predicates: &mut HashSet<PredicateRef<'a>>) {
        match self {
            App(Predicate(name), args) => {
                let arg_count = args.len();
                if let Some(existing_count) = predicates
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.args.len())
                {
                    if existing_count != arg_count {
                        panic!(
                            "Predicate '{}' previously defined with {} arguments, now with {} arguments",
                            name, existing_count, arg_count
                        );
                    }
                } else {
                    predicates.insert(PredicateRef { name, args });
                }
                for arg in args {
                    arg.extract_predicates(predicates);
                }
            }
            App(_, args) => {
                for arg in args {
                    arg.extract_predicates(predicates);
                }
            }
            _ => {}
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Var(name) => write!(f, "|{}|", name), // we always quote variable names for simplicity
            Const(value) => write!(f, "{}", value),
            ConstTrue => write!(f, "true"),
            App(op, args) => {
                write!(f, "({}", op)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct HornClause {
    pub(crate) head: Expr,
    pub(crate) body: Vec<Expr>,
}

impl HornClause {
    fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_free_vars_expr(&self.head, &mut vars);
        for expr in &self.body {
            self.collect_free_vars_expr(expr, &mut vars);
        }
        vars
    }

    fn collect_free_vars_expr(&self, expr: &Expr, vars: &mut HashSet<String>) {
        match expr {
            Expr::Var(name) => {
                vars.insert(name.clone());
            }
            Expr::Const(_) => {}
            Expr::ConstTrue => {}
            Expr::App(_, args) => {
                for arg in args {
                    self.collect_free_vars_expr(arg, vars);
                }
            }
        }
    }

    fn extract_predicates<'a>(&'a self, predicates: &mut HashSet<PredicateRef<'a>>) {
        self.head.extract_predicates(predicates);
        for expr in &self.body {
            expr.extract_predicates(predicates);
        }
    }
}

impl Display for HornClause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let vars: Vec<String> = self.free_vars().into_iter().collect();
        write!(f, "(assert (forall ((|{}| Int)", vars[0])?;
        for var in &vars[1..] {
            write!(f, " (|{}| Int)", var)?;
        }
        let body = if self.body.is_empty() {
            ConstTrue
        } else {
            App(Operation::And, self.body.clone())
        };
        write!(f, ") (=> {} {})))", body, self.head)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Modulo,
    And,
    Or,
    Equals,
    NotEquals,
    LessThan,
    LessEquals,
    GreaterThan,
    GreaterEquals,
    Predicate(String),
}

impl Operation {
    pub fn predicate<S: Into<String>>(name: S) -> Self {
        Predicate(name.into())
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Operation::Add => write!(f, "+"),
            Operation::Sub => write!(f, "-"),
            Operation::Mul => write!(f, "*"),
            Operation::Div => write!(f, "/"),
            Operation::Modulo => write!(f, "mod"),
            Operation::And => write!(f, "and"),
            Operation::Or => write!(f, "or"),
            Operation::Equals => write!(f, "="),
            Operation::NotEquals => write!(f, "distinct"),
            Operation::LessThan => write!(f, "<"),
            Operation::LessEquals => write!(f, "<="),
            Operation::GreaterThan => write!(f, ">"),
            Operation::GreaterEquals => write!(f, ">="),
            Operation::Predicate(name) => write!(f, "{}", name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct PredicateRef<'a> {
    pub(crate) name: &'a String,
    args: &'a Vec<Expr>,
}

impl PredicateRef<'_> {
    fn args_for_next_query(&self) -> Vec<Expr> {
        self.args
            .iter()
            .map(|arg| match arg {
                Var(name) => {
                    let mut new_name = name.clone();
                    while new_name.ends_with('\'') {
                        new_name.pop();
                    }
                    Var(new_name)
                }
                _ => panic!("Non-variable argument in predicate reference"),
            })
            .collect()
    }

    pub(crate) fn to_enum(&self) -> Expr {
        App(Predicate(self.name.clone()), self.args_for_next_query())
    }
}

pub(crate) trait HornClauseVecOperations<'a> {
    fn _extract_unique_predicates(&self) -> Vec<PredicateRef<'_>>;
    fn generate_predicate_declarations(&self) -> Vec<String>;
    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause;
    fn get_latest_query(&self) -> Option<PredicateRef>;
}

impl<'a> HornClauseVecOperations<'a> for Vec<HornClause> {
    fn _extract_unique_predicates(&self) -> Vec<PredicateRef<'_>> {
        let mut unique_predicates = HashSet::new();
        for clause in self {
            clause.extract_predicates(&mut unique_predicates);
        }
        let mut predicates = unique_predicates
            .iter()
            .map(|x| x.clone())
            .collect::<Vec<PredicateRef>>();
        predicates.sort_by(|a, b| a.name.cmp(b.name));
        predicates
    }

    fn generate_predicate_declarations(&self) -> Vec<String> {
        let mut predicates = self._extract_unique_predicates();
        predicates.sort_by(|a, b| a.name.cmp(b.name));
        predicates
            .iter()
            .map(|PredicateRef { name, args }| {
                let arg_types = (0..args.len())
                    .map(|_| "Int")
                    .collect::<Vec<&str>>()
                    .join(" ");
                format!("(declare-fun {} ({}) Bool)", name, arg_types)
            })
            .collect()
    }

    #[allow(non_snake_case)]
    fn create_next_CHC(&self) -> HornClause {
        let prev_query = self.get_latest_query();
        let query_params = prev_query
            .as_ref()
            .map(|query| query.args_for_next_query())
            .unwrap_or_else(Vec::new);

        let new_query_name = unsafe { utils::get_new_query_name() };
        let new_query = App(Predicate(new_query_name), query_params);

        let body = prev_query
            .map(|query| vec![query.to_enum()])
            .unwrap_or_else(Vec::new);

        HornClause {
            head: new_query,
            body,
        }
    }

    fn get_latest_query(&self) -> Option<PredicateRef> {
        self.last().map({
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
}
