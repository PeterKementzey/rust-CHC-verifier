use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::io::Write;

use itertools::sorted;

use crate::smtlib2::Expr::{App, Const, ConstTrue, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::Operation::Predicate;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    Var(String),
    Const(i32),
    ConstTrue,
    ReferenceCurrVal(String),
    ReferenceFinalVal(String),
    App(Operation, Vec<Expr>),
}

impl Expr {
    fn extract_predicates<'a>(&'a self, predicates: &mut HashSet<PredicateRef<'a>>) {
        match self {
            App(Predicate(name), args) => {
                let arg_count = args.len();
                if let Some(existing_count) = predicates
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.args.len())
                {
                    assert_eq!(existing_count, arg_count, "Predicate '{name}' previously defined with {existing_count} arguments, now with {arg_count} arguments");
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
            Var(name) => write!(f, "|{name}|"), // we always quote variable names for simplicity
            Const(value) => write!(f, "{value}"),
            ConstTrue => write!(f, "true"),
            // predicates can have 0 arguments, in which case Z3 does not accept parentheses
            App(ref pred @ Predicate(_), args) if args.is_empty() => write!(f, "{pred}"),
            App(op, args) => {
                write!(f, "({op}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            ReferenceCurrVal(name) => write!(f, "|{}|", current_value_repr(name)),
            ReferenceFinalVal(name) => write!(f, "|{}|", final_value_repr(name)),
        }
    }
}

fn current_value_repr(var_name: &String) -> String {
    format!("{var_name}*")
}

fn final_value_repr(var_name: &String) -> String {
    format!("{var_name}^")
}

#[derive(Debug, Clone)]
pub(crate) struct HornClause {
    pub(crate) head: Expr,
    pub(crate) body: Vec<Expr>,
}

impl HornClause {
    fn free_vars(&self) -> HashSet<String> {
        fn collect_free_vars_from_expr(expr: &Expr, vars: &mut HashSet<String>) {
            match expr {
                Var(name) => {
                    vars.insert(name.clone());
                }
                ReferenceCurrVal(name) => {
                    vars.insert(current_value_repr(name));
                }
                ReferenceFinalVal(name) => {
                    vars.insert(final_value_repr(name));
                }
                Const(_) | ConstTrue => {}
                App(_, args) => {
                    for arg in args {
                        collect_free_vars_from_expr(arg, vars);
                    }
                }
            }
        }

        let mut vars = HashSet::new();
        collect_free_vars_from_expr(&self.head, &mut vars);
        for expr in &self.body {
            collect_free_vars_from_expr(expr, &mut vars);
        }
        vars
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
        let vars: Vec<String> = sorted(self.free_vars()).collect();
        write!(f, "(assert (forall ((|{}| Int)", vars[0])?;
        for var in &vars[1..] {
            write!(f, " (|{var}| Int)")?;
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
    Not,
    Equals,
    NotEquals,
    LessThan,
    LessEquals,
    GreaterThan,
    GreaterEquals,
    Predicate(String),
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
            Operation::Not => write!(f, "not"),
            Operation::Equals => write!(f, "="),
            Operation::NotEquals => write!(f, "distinct"),
            Operation::LessThan => write!(f, "<"),
            Operation::LessEquals => write!(f, "<="),
            Operation::GreaterThan => write!(f, ">"),
            Operation::GreaterEquals => write!(f, ">="),
            Operation::Predicate(name) => write!(f, "{name}"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct PredicateRef<'a> {
    name: &'a String,
    args: &'a Vec<Expr>,
}

impl PredicateRef<'_> {
    pub(crate) fn from<'a>(name: &'a String, args: &'a Vec<Expr>) -> PredicateRef<'a> {
        PredicateRef { name, args }
    }

    pub(crate) fn get_name_and_args(&self) -> (&String, &Vec<Expr>) {
        (self.name, self.args)
    }
}

pub(crate) trait Smtlib2Display {
    fn write_as_smtlib2(&self, output: Box<dyn Write>) -> std::io::Result<()>;
}

impl Smtlib2Display for Vec<HornClause> {
    fn write_as_smtlib2(&self, mut output: Box<dyn Write>) -> std::io::Result<()> {
        writeln!(output, "(set-logic HORN)")?;
        writeln!(output, "(set-option :fp.engine spacer)")?;
        writeln!(output, "(set-option :model true)\n")?;
        for decl in self.generate_predicate_declarations() {
            writeln!(output, "{decl}")?;
        }
        for clause in self {
            writeln!(output, "{clause}")?;
        }
        writeln!(output, "\n(check-sat)")?;
        writeln!(output, "(get-model)")
    }
}

trait CHCSystem {
    fn extract_unique_predicates(&self) -> Vec<PredicateRef<'_>>;
    fn generate_predicate_declarations(&self) -> Vec<String>;
}

impl CHCSystem for Vec<HornClause> {
    fn extract_unique_predicates(&self) -> Vec<PredicateRef<'_>> {
        fn get_query_num(name: &str) -> usize {
            name[1..].parse().unwrap()
        }

        let mut unique_predicates = HashSet::new();
        for clause in self {
            clause.extract_predicates(&mut unique_predicates);
        }
        let mut predicates: Vec<PredicateRef> = unique_predicates.into_iter().collect();
        predicates.sort_by(|a, b| get_query_num(a.name).cmp(&get_query_num(b.name)));
        predicates
    }

    fn generate_predicate_declarations(&self) -> Vec<String> {
        self.extract_unique_predicates()
            .iter()
            .map(|PredicateRef { name, args }| {
                let arg_types = (0..args.len())
                    .map(|_| "Int")
                    .collect::<Vec<&str>>()
                    .join(" ");
                format!("(declare-fun {name} ({arg_types}) Bool)")
            })
            .collect()
    }
}
