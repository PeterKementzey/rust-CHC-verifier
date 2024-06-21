use syn::ExprAssign;

use crate::smtlib2;
use crate::smtlib2::Expr::{App, Const, ReferenceCurrVal, Var};
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::{
    Add, And, Div, Equals, GreaterEquals, GreaterThan, LessEquals, LessThan, Modulo, Mul, Not,
    NotEquals, Or, Sub,
};
use crate::syn_utils::get_var_name;
use crate::translate::borrow_utils;
use crate::translate::borrow_utils::drop_reference;
use crate::translate::utils::{AliasGroups, CHCSystem};

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

pub(super) fn translate_assignment(
    assign: &ExprAssign,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &mut AliasGroups,
) {
    fn case_borrow(
        _lhs: &smtlib2::Expr,
        _initial_value: &syn::Expr,
        #[allow(non_snake_case)] _CHCs: &mut Vec<HornClause>,
    ) {
        unimplemented!("Borrow not implemented yet")
    }

    fn case_create_alias(
        lhs: &smtlib2::Expr,
        rhs_name: &str,
        alias_groups: &mut AliasGroups,
        query_params: &[smtlib2::Expr],
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        // if we are creating a new alias the lhs should just be a variable, not dereferenced
        let lhs_name = match &lhs {
            Var(name) => {
                let alias_curr_name = alias_groups.find_curr_name(name).unwrap_or(name);
                assert!(query_params.contains(&ReferenceCurrVal(alias_curr_name.clone())));
                name.clone()
            }
            _ => panic!("Left hand side is not a variable"),
        };

        drop_reference(&lhs_name, CHCs, alias_groups);
        alias_groups.add_alias(rhs_name.to_string(), lhs_name.clone());
    }

    fn case_integer_assign(
        lhs: &smtlib2::Expr,
        rhs: smtlib2::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let updated_lhs = {
            match lhs.clone() {
                Var(name) => Var(name + "'"),
                ReferenceCurrVal(name) => ReferenceCurrVal(name + "'"),
                _ => panic!("Assignment left-hand side is not a variable"),
            }
        };
        let mut new_clause = CHCs.create_next_CHC();
        let assignment: smtlib2::Expr = App(Equals, vec![updated_lhs.clone(), rhs]);
        new_clause.body.push(assignment);
        new_clause.replace_head_query_param(lhs, updated_lhs);
        CHCs.push(new_clause);
    }

    assert!(!CHCs.is_empty(), "Assignment reached with no CHCs");

    let lhs: smtlib2::Expr = translate_syn_expr(&assign.left, alias_groups);
    let rhs: &syn::Expr = &assign.right;

    let query_params = CHCs
        .get_latest_query()
        .expect("Impossible to have assignment before any queries are created (no variables to assign to)")
        .get_stripped_query_params();

    borrow_utils::translate_assignment(
        &lhs,
        rhs,
        CHCs,
        &query_params,
        alias_groups,
        case_borrow,
        case_create_alias,
        case_integer_assign,
    );
}
