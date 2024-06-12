use crate::smtlib2;
use crate::smtlib2::Expr::*;
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::*;
use crate::syn_utils::{
    get_assert_condition, get_declared_var_name, get_macro_name, get_referenced_name,
};
use crate::translate::expr_translations::translate_syn_expr;
use crate::translate::utils::CHCSystem;

pub(super) fn translate_local_var_decl(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let new_query_param = Var(get_declared_var_name(&local));

    let mut new_clause = CHCs.create_next_CHC();
    if new_clause.head_contains(&new_query_param) {
        panic!("New query parameter name already exists in latest query")
    }

    new_clause.insert_head_query_param(new_query_param.clone());

    let rhs = local
        .init
        .as_ref()
        .map(|syn::LocalInit { expr, .. }| translate_syn_expr(&expr));

    if let Some(rhs) = rhs {
        let assignment = App(Equals, vec![new_query_param, rhs]);
        new_clause.body.push(assignment);
    }

    CHCs.push(new_clause);
}

pub(super) fn translate_borrow(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let reference_name = get_declared_var_name(&local);
    let referenced_name = local
        .init
        .as_ref()
        .map(|syn::LocalInit { expr, .. }| get_referenced_name(&expr))
        .expect("Cannot get reference target");

    let referenced_var = Var(referenced_name.clone());
    let current_value = ReferenceCurrVal(reference_name.clone());
    let final_value = ReferenceFinalVal(reference_name);

    let mut new_clause = CHCs.create_next_CHC();

    if new_clause.head_contains(&current_value) {
        panic!("Reference already exists in latest query")
    }
    if new_clause.head_contains(&final_value) {
        panic!("Final value already exists in latest query")
    }
    if !new_clause.head_contains(&referenced_var) {
        panic!("Referenced variable not found in latest query")
    }

    new_clause.insert_head_query_param(current_value.clone());
    new_clause.insert_head_query_param(final_value.clone());

    let curr_val_eq_referenced = App(Equals, vec![current_value, referenced_var.clone()]);
    new_clause.body.push(curr_val_eq_referenced);

    let referenced_var_updated = Var(referenced_name + "'");
    let referenced_eq_final_val = App(Equals, vec![referenced_var_updated.clone(), final_value]);
    new_clause.body.push(referenced_eq_final_val);
    new_clause.replace_head_query_param(&referenced_var, referenced_var_updated);

    CHCs.push(new_clause);
}

pub(super) fn translate_drop(
    var_name: &String,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    if let App(Predicate(_), query_params) = CHCs
        .get_latest_query()
        .expect("No queries to drop reference from")
        .to_expr_without_trailing_apostrophes() {
        query_params.iter().find_map(|v| match v {
            var@Var(name) if name == var_name => {
                let mut new_clause = CHCs.create_next_CHC();
                let head_query_params = new_clause.get_mut_head_query_params();
                head_query_params.retain(|v| v != var);
                CHCs.push(new_clause);
                Some(())
            }
            curr_val @ ReferenceCurrVal(name) if name == var_name => {
                let mut new_clause = CHCs.create_next_CHC();
                let head_query_params = new_clause.get_mut_head_query_params();
                let final_val = ReferenceFinalVal(name.clone());
                head_query_params.retain(|v| v != curr_val && *v != final_val);
                let final_val_eq_curr_val = App(Equals, vec![final_val, curr_val.clone()]);
                new_clause.body.push(final_val_eq_curr_val);
                CHCs.push(new_clause);
                Some(())
            }
            Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_) => None,
            _ => panic!("Unexpected query parameter: {:?}", v),
        }).expect("Variable not found in latest query");
    }
}

pub(super) fn translate_assertion(
    stmt_macro: &syn::StmtMacro,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let macro_name = get_macro_name(&stmt_macro);
    if macro_name != "assert" {
        panic!("Unsupported macro name: {}", macro_name);
    }

    let condition: syn::Expr = get_assert_condition(&stmt_macro);
    let condition: smtlib2::Expr = translate_syn_expr(&condition);

    let last_query = CHCs
        .get_latest_query()
        .expect("No queries to assert against")
        .to_expr_without_trailing_apostrophes();
    let new_clause = HornClause {
        head: condition,
        body: vec![last_query],
    };
    CHCs.push(new_clause);
}
