use syn::PatIdent;

use crate::smtlib2::Expr::*;
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::*;
use crate::translate::utils;
use crate::translate::utils::get_latest_query;

pub(crate) fn translate_local_var_decl(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let new_var_name = match &local.pat {
        syn::Pat::Ident(PatIdent { ident, .. }) => ident.to_string(),
        _ => panic!("Local variable declaration pattern is not an identifier"),
    };
    let new_query_param = Var(new_var_name);

    let prev_query = get_latest_query(&CHCs);
    let mut query_params = prev_query
        .map(|query| query.args.clone())
        .unwrap_or_else(|| Vec::new());
    if query_params.contains(&new_query_param) {
        panic!("New query parameter name already exists in latest query")
    }
    query_params.push(new_query_param);

    let new_query_name = unsafe { utils::get_new_query_name() };
    let new_query = App(Predicate(new_query_name), query_params);
    let new_clause = HornClause {
        head: new_query,
        body: vec![ConstTrue], // TODO
    };
    CHCs.push(new_clause);
}
