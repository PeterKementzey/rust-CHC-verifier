use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    Var(String),
    Const(i32),
    ConstTrue,
    App(Operation, Vec<Expr>),
}

impl Expr {
    pub fn var<S: Into<String>>(name: S) -> Self {
        Expr::Var(name.into())
    }

    fn extract_predicates<'a>(&'a self, predicates: &mut HashSet<PredicateRef<'a>>) {
        match self {
            Expr::App(Operation::Predicate(name), args) => {
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
            Expr::App(_, args) => {
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
            Expr::Var(name) => write!(f, "|{}|", name), // we always quote variable names for simplicity
            Expr::Const(value) => write!(f, "{}", value),
            Expr::ConstTrue => write!(f, "true"),
            Expr::App(op, args) => {
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
        write!(f, ") (=> (and")?;
        for expr in &self.body {
            write!(f, " {}", expr)?;
        }
        write!(f, ") {})))", self.head)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Operation {
    GreaterThan,
    LessThan,
    Equals,
    Plus,
    Predicate(String),
}

impl Operation {
    pub fn predicate<S: Into<String>>(name: S) -> Self {
        Operation::Predicate(name.into())
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Operation::GreaterThan => write!(f, ">"),
            Operation::LessThan => write!(f, "<"),
            Operation::Equals => write!(f, "="),
            Operation::Plus => write!(f, "+"),
            Operation::Predicate(name) => write!(f, "{}", name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct PredicateRef<'a> {
    pub(crate) name: &'a String,
    pub(crate) args: &'a Vec<Expr>,
}

fn extract_unique_predicates<'a>(clauses: &'a Vec<HornClause>) -> HashSet<PredicateRef<'a>> {
    let mut predicates = HashSet::new();
    for clause in clauses {
        clause.extract_predicates(&mut predicates);
    }
    predicates
}

pub(crate) fn generate_predicate_declarations(
    #[allow(non_snake_case)] CHCs: &Vec<HornClause>,
) -> Vec<String> {
    let unique_predicates = extract_unique_predicates(CHCs);
    let mut predicates = unique_predicates.iter().collect::<Vec<&PredicateRef>>();
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
