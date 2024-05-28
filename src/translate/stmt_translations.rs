use crate::smtlib2;
use crate::smtlib2::Expr::*;
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::*;
use crate::translate::expr_translations::translate_syn_expr;
use crate::translate::utils::CHCSystem;

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

pub(crate) fn translate_assertion(
    stmt_macro: &syn::StmtMacro,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let macro_name = stmt_macro.mac.path.segments[0].ident.to_string();
    if macro_name != "assert" {
        panic!("Unsupported macro name: {}", macro_name);
    }

    let condition: syn::Expr = syn::parse2(stmt_macro.mac.tokens.clone())
        .expect("Failed to parse macro tokens as expression");
    let condition: smtlib2::Expr = translate_syn_expr(&condition);

    let last_query = CHCs
        .get_latest_query()
        .expect("No queries to assert against");
    let new_clause = HornClause {
        head: condition,
        body: vec![last_query.to_stripped_enum()],
    };
    CHCs.push(new_clause);
}
