use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    Var(String),
    Const(i32),
    App(Operation, Vec<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(name) => write!(f, "{}", name),
            Expr::Const(value) => write!(f, "{}", value),
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
            Expr::App(_, args) => {
                for arg in args {
                    self.collect_free_vars_expr(arg, vars);
                }
            }
        }
    }
}

impl Display for HornClause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let vars: Vec<String> = self.free_vars().into_iter().collect();
        write!(f, "assert (forall (")?;
        for var in &vars {
            write!(f, " ({} Int)", var)?;
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
    Predicate(String),
}

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Operation::GreaterThan => write!(f, ">"),
            Operation::LessThan => write!(f, "<"),
            Operation::Equals => write!(f, "="),
            Operation::Predicate(name) => write!(f, "{}", name),
        }
    }
}
