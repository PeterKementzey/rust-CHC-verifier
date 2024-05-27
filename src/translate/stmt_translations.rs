use crate::smtlib2::Expr::*;
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::*;
use crate::translate::utils::CHCSystem;
use crate::translate::expr_translations::translate_syn_expr;

pub(crate) fn translate_local_var_decl(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let new_var_name = match &local.pat {
        syn::Pat::Ident(syn::PatIdent { ident, .. }) => ident.to_string(),
        _ => panic!("Local variable declaration pattern is not an identifier"),
    };
    let new_query_param = Var(new_var_name);

    let mut new_clause = CHCs.create_next_CHC();
    if let Some(App(Predicate(_), prev_query_params)) = &new_clause.body.get(0) {
        if prev_query_params.contains(&new_query_param) {
            panic!("New query parameter name already exists in latest query")
        }
    }

    if let App(Predicate(_), new_query_params) = &mut new_clause.head {
        new_query_params.push(new_query_param.clone());
    }

    let rhs = local.init.as_ref().map(
        |syn::LocalInit {
             eq_token: _,
             expr,
             diverge: _,
         }| translate_syn_expr(&expr),
    );

    if let Some(rhs) = rhs {
        let assignment = App(Equals, vec![new_query_param, rhs]);
        new_clause.body.push(assignment);
    }

    CHCs.push(new_clause);
}
