use crate::smtlib2;
use crate::smtlib2::Expr::{App, Const, ReferenceCurrVal, Var};
use crate::smtlib2::Operation::{
    Add, And, Div, Equals, GreaterEquals, GreaterThan, LessEquals, LessThan, Modulo, Mul, Not,
    NotEquals, Or, Sub,
};
use crate::syn_utils::get_var_name;
use crate::translate::utils::AliasGroups;

pub(super) fn translate_syn_expr(expr: &syn::Expr, alias_groups: &AliasGroups) -> smtlib2::Expr {
    match expr {
        // Binary operation
        syn::Expr::Binary(binary) => {
            let left = translate_syn_expr(&binary.left, alias_groups);
            let right = translate_syn_expr(&binary.right, alias_groups);
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
        // Unary operation
        syn::Expr::Unary(unary) => {
            let expr = translate_syn_expr(&unary.expr, alias_groups);
            match unary.op {
                syn::UnOp::Not(_) => App(Not, vec![expr]),
                syn::UnOp::Neg(_) => App(Sub, vec![Const(0), expr]),
                syn::UnOp::Deref(_) => {
                    // If we are dereferencing a variable, it has to be a reference (borrow)
                    if let Var(name) = expr {
                        ReferenceCurrVal(
                            alias_groups.find_curr_name(&name).unwrap_or(&name).clone(),
                        )
                    } else {
                        panic!("Dereference of non-variable")
                    }
                }
                _ => panic!("Unsupported unary operator: {:?}", unary.op),
            }
        }
        // Parentheses
        syn::Expr::Paren(paren) => translate_syn_expr(&paren.expr, alias_groups),
        // Variable
        syn::Expr::Path(path) => Var(get_var_name(path)),
        // Integer constant
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit_int),
            ..
        }) => Const(lit_int.base10_parse::<i32>().expect("Cannot parse integer")),

        _ => panic!("Unsupported syn expression, got: {expr:?}"),
    }
}