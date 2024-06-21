use crate::smtlib2;
use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::Equals;
use crate::syn_utils::is_borrow;
use crate::translate::expr_translations::translate_syn_expr;
use crate::translate::utils::{AliasGroups, CHCSystem};

pub(super) fn drop_reference(
    reference_name: &String,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &mut AliasGroups,
) {
    let mut new_clause = CHCs.create_next_CHC();
    let old_curr_val = ReferenceCurrVal(reference_name.clone());
    let old_final_val = ReferenceFinalVal(reference_name.clone());
    if let Some(curr_name) = alias_groups.find_curr_name(reference_name) {
        // if part of an alias group, drop the alias (and possibly change current name of group)
        let curr_name = curr_name.clone();
        if curr_name == *reference_name {
            alias_groups.shift_curr_name_in_group(&curr_name);
            let new_curr_name = alias_groups.find_curr_name(&curr_name).unwrap();
            let new_curr_val = ReferenceCurrVal(new_curr_name.clone());
            let new_final_val = ReferenceFinalVal(new_curr_name.clone());
            assert!(
                !new_clause.head_contains(&new_curr_val),
                "Reference already exists in latest query"
            );
            new_clause.replace_head_query_param(&old_curr_val, new_curr_val.clone());
            new_clause.replace_head_query_param(&old_final_val, new_final_val.clone());
            let new_curr_val_eq_old_curr_val = App(Equals, vec![new_curr_val, old_curr_val]);
            let new_final_val_eq_old_final_val = App(Equals, vec![new_final_val, old_final_val]);
            new_clause.body.push(new_curr_val_eq_old_curr_val);
            new_clause.body.push(new_final_val_eq_old_final_val);
        }
        alias_groups.drop_alias(reference_name);
    } else {
        // if there are no aliases, then finalize the reference
        let head_query_params = new_clause.get_mut_head_query_params();
        head_query_params.retain(|v| *v != old_curr_val && *v != old_final_val);
        let final_val_eq_curr_val = App(Equals, vec![old_final_val.clone(), old_curr_val.clone()]);
        new_clause.body.push(final_val_eq_curr_val);
    }
    CHCs.push(new_clause);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn translate_assignment<LhsType>(
    lhs_name: &LhsType,
    rhs: &syn::Expr,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    query_params: &[smtlib2::Expr],
    alias_groups: &mut AliasGroups,
    case_borrow: fn(&LhsType, &syn::Expr, &mut Vec<HornClause>),
    case_create_alias: fn(&LhsType, &str, &mut AliasGroups, &[smtlib2::Expr], &mut Vec<HornClause>),
    case_integer_assign: fn(&LhsType, smtlib2::Expr, &mut Vec<HornClause>),
) {
    if is_borrow(rhs) {
        case_borrow(lhs_name, rhs, CHCs); // option 1: borrow - we know this from syntax
    } else {
        let rhs: smtlib2::Expr = translate_syn_expr(rhs, alias_groups);

        match rhs {
            // if we are creating an alias then from syntax rhs seems like a `Var`, but is actually a `ReferenceCurrVal`
            Var(rhs_name)
                if {
                    let alias_curr_name =
                        alias_groups.find_curr_name(&rhs_name).unwrap_or(&rhs_name);
                    query_params.contains(&ReferenceCurrVal(alias_curr_name.clone()))
                } =>
            {
                case_create_alias(lhs_name, &rhs_name, alias_groups, query_params, CHCs);
                // option 2: create alias - we know from query params whether rhs is a reference
            }

            _ => case_integer_assign(lhs_name, rhs, CHCs), // option 3: integer assignment - if neither of the above
        }
    }
}

#[allow(clippy::similar_names)]
/// Assumes reference (curr & final) is already present in head query params, referenced variable as well but not with apostrophe
pub(super) fn borrow_variable(
    reference_name: &str,
    referenced_name: &str,
    new_clause: &mut HornClause,
) {
    let referenced_var = Var(referenced_name.to_string());
    let current_value = ReferenceCurrVal(reference_name.to_string());
    let final_value = ReferenceFinalVal(reference_name.to_string());
    let referenced_var_updated = Var(referenced_name.to_string() + "'");

    assert!(
        new_clause.head_contains(&current_value),
        "Reference does not exist in latest query"
    );
    assert!(
        new_clause.head_contains(&final_value),
        "Final value does not exist in latest query"
    );
    assert!(
        new_clause.head_contains(&referenced_var),
        "Referenced variable not found in latest query"
    );
    assert!(
        !new_clause.head_contains(&referenced_var_updated),
        "Referenced variable updated already present in query parameters"
    );

    let curr_val_eq_referenced = App(Equals, vec![current_value, referenced_var.clone()]);
    new_clause.body.push(curr_val_eq_referenced);

    let referenced_eq_final_val = App(Equals, vec![referenced_var_updated.clone(), final_value]);
    new_clause.body.push(referenced_eq_final_val);
    new_clause.replace_head_query_param(&referenced_var, referenced_var_updated);
}
