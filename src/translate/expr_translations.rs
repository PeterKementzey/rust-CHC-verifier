use syn::ExprAssign;

use crate::smtlib2;
use crate::smtlib2::Expr::*;
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::*;
use crate::syn_utils::get_var_name;
use crate::translate::utils::CHCSystem;

pub(super) fn translate_syn_expr(expr: &syn::Expr) -> smtlib2::Expr {
    match expr {
        // Binary operation
        syn::Expr::Binary(binary) => {
            let left = translate_syn_expr(&binary.left);
            let right = translate_syn_expr(&binary.right);
            match binary.op {
                syn::BinOp::Add(_) => App(Add, vec![left, right]),
                syn::BinOp::Sub(_) => App(Sub, vec![left, right]),
                syn::BinOp::Mul(_) => App(Mul, vec![left, right]),
                syn::BinOp::Div(_) => App(Div, vec![left, right]),
                syn::BinOp::Rem(_) => App(Modulo, vec![left, right]),
                syn::BinOp::And(_) => App(And, vec![left, right]),
                syn::BinOp::Or(_) => App(Or, vec![left, right]),
                // Bit operations not implemented for now
                // syn::BinOp::BitXor(_) => App(BitXor, vec![left, right]),
                // syn::BinOp::BitAnd(_) => App(BitAnd, vec![left, right]),
                // syn::BinOp::BitOr(_) => App(BitOr, vec![left, right]),
                // syn::BinOp::Shl(_) => App(Shl, vec![left, right]),
                // syn::BinOp::Shr(_) => App(Shr, vec![left, right]),
                syn::BinOp::Eq(_) => App(Equals, vec![left, right]),
                syn::BinOp::Ne(_) => App(NotEquals, vec![left, right]),
                syn::BinOp::Lt(_) => App(LessThan, vec![left, right]),
                syn::BinOp::Le(_) => App(LessEquals, vec![left, right]),
                syn::BinOp::Gt(_) => App(GreaterThan, vec![left, right]),
                syn::BinOp::Ge(_) => App(GreaterEquals, vec![left, right]),
                _ => panic!("Unsupported binary operator: {:?}", binary.op),
            }
        }
        // Variable
        syn::Expr::Path(path) => Var(get_var_name(&path)),
        // Integer constant
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit_int),
            ..
        }) => Const(lit_int.base10_parse::<i32>().unwrap()),

        _ => panic!("Unsupported syn expression, got: {:?}", expr),
    }
}

pub(super) fn translate_assignment(
    assign: &ExprAssign,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    if CHCs.is_empty() {
        panic!("Assignment reached with no CHCs")
    }

    let (lhs, updated_lhs) = {
        let variable_name = match translate_syn_expr(&assign.left) {
            Var(name) => name,
            _ => panic!("Assignment left-hand side is not a variable"),
        };
        let mut new_name = variable_name.clone();
        new_name.push('\''); // variable_name'
        (Var(variable_name), Var(new_name))
    };

    let mut new_clause = CHCs.create_next_CHC();

    let rhs: smtlib2::Expr = translate_syn_expr(&assign.right);
    let assignment: smtlib2::Expr = App(Equals, vec![updated_lhs.clone(), rhs]);
    new_clause.body.push(assignment);
    new_clause.replace_head_query_param(&lhs, updated_lhs);

    CHCs.push(new_clause);
}
