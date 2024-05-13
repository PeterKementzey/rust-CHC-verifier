use String as Variable;

enum Expression {
    Predicate(Predicate),
    Conjunction(Conjunction),
    ConstrainedHornClause(ConstrainedHornClause),
}

trait SMTLib2 {
    fn to_smtlib2(&self) -> String;
}

impl SMTLib2 for Expression {
    fn to_smtlib2(&self) -> String {
        match self {
            Expression::Predicate(predicate) => predicate.to_smtlib2(),
            Expression::Conjunction(conjunction) => conjunction.to_smtlib2(),
            Expression::ConstrainedHornClause(constrained_horn_clause) => {
                constrained_horn_clause.to_smtlib2()
            }
        }
    }
}

struct Predicate {
    name: String,
    args: Vec<Variable>,
}

impl SMTLib2 for Predicate {
    fn to_smtlib2(&self) -> String {
        String::from("Predicate") // TODO
    }
}

struct Conjunction {
    expressions: Vec<Box<Expression>>,
}

impl SMTLib2 for Conjunction {
    fn to_smtlib2(&self) -> String {
        let mut s_expr = String::from("(and ");
        for expr in &self.expressions {
            s_expr.push_str(&expr.to_smtlib2());
            s_expr.push(' ');
        }
        s_expr.pop();
        s_expr.push(')');
        s_expr
    }
}

struct ConstrainedHornClause {
    head: Predicate,
    body: Option<Box<Expression>>,
}

impl SMTLib2 for ConstrainedHornClause {
    fn to_smtlib2(&self) -> String {
        String::from("ConstrainedHornClause") // TODO
    }
}
