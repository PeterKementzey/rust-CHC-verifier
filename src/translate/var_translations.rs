use syn::ExprAssign;

use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::Equals;
use crate::syn_utils::{get_borrowed_name, get_declared_var_name};
use crate::translate::syn_expr_translation::translate_syn_expr;
use crate::translate::utils::{AliasGroups, CHCSystem};
use crate::translate::var_translations::util::{assign, borrow_variable, drop_reference};
use crate::{smtlib2, syn_utils};

///  Local variable initialization can be one of the following:
///  - If the new variable is a reference then
///     - Either we are newly borrowing a variable
///     - Or we are creating a new alias from another reference variable
///  - If the new variable is an integer then it's just an assignment initialization
pub(super) fn translate_local_var_decl(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &mut AliasGroups,
) {
    #[allow(clippy::similar_names)]
    fn case_borrow(
        #[allow(clippy::ptr_arg)] reference_name: &String,
        initial_value: &syn::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let referenced_name = get_borrowed_name(initial_value);
        let referenced_var = Var(referenced_name.clone());
        let current_value = ReferenceCurrVal(reference_name.clone());
        let final_value = ReferenceFinalVal(reference_name.clone());

        let mut new_clause = CHCs.create_next_CHC();

        assert!(
            !new_clause.head_contains(&current_value),
            "Reference already exists in latest query"
        );
        assert!(
            !new_clause.head_contains(&final_value),
            "Final value already exists in latest query"
        );
        assert!(
            new_clause.head_contains(&referenced_var),
            "Referenced variable not found in latest query"
        );

        new_clause.insert_head_query_param(current_value.clone());
        new_clause.insert_head_query_param(final_value.clone());

        borrow_variable(reference_name, &referenced_name, &mut new_clause);

        CHCs.push(new_clause);
    }

    fn case_create_alias(
        new_alias_name: &String,
        rhs_name: &str,
        alias_groups: &mut AliasGroups,
        _query_params: &[smtlib2::Expr],
        #[allow(non_snake_case)]
        #[allow(clippy::ptr_arg)]
        _CHCs: &mut Vec<HornClause>,
    ) {
        alias_groups.add_alias(rhs_name.to_string(), new_alias_name.to_string());
    }

    fn case_integer_init(
        #[allow(clippy::ptr_arg)] new_var_name: &String,
        rhs: smtlib2::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let new_query_param = Var(new_var_name.clone());
        let mut new_clause = CHCs.create_next_CHC();
        assert!(
            !new_clause.head_contains(&new_query_param),
            "New query parameter name already exists in latest query"
        );

        new_clause.insert_head_query_param(new_query_param.clone());

        let assignment = App(Equals, vec![new_query_param, rhs]);
        new_clause.body.push(assignment);

        CHCs.push(new_clause);
    }

    let query_params: Vec<smtlib2::Expr> = CHCs
        .get_latest_query()
        .into_iter()
        .flat_map(|q| q.get_stripped_query_params())
        .collect();

    assign(
        &get_declared_var_name(local),
        syn_utils::get_init_expr(local).expect("Local variable not initialized"),
        CHCs,
        &query_params,
        alias_groups,
        case_borrow,
        case_create_alias,
        case_integer_init,
    );
}

pub(super) fn translate_assignment(
    assignment: &ExprAssign,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &mut AliasGroups,
) {
    fn case_borrow(
        _lhs: &smtlib2::Expr,
        _initial_value: &syn::Expr,
        #[allow(non_snake_case)]
        #[allow(clippy::ptr_arg)]
        _CHCs: &mut Vec<HornClause>,
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

    let lhs: smtlib2::Expr = translate_syn_expr(&assignment.left, alias_groups);
    let rhs: &syn::Expr = &assignment.right;

    let query_params = CHCs
        .get_latest_query()
        .expect("Impossible to have assignment before any queries are created (no variables to assign to)")
        .get_stripped_query_params();

    assign(
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

pub(super) fn translate_drop(
    var_name: &String,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &mut AliasGroups,
) {
    let query_params = CHCs
        .get_latest_query()
        .expect("No queries to drop reference from")
        .get_stripped_query_params();

    query_params
        .iter()
        .find_map(|v| match v {
            var @ Var(name) if name == var_name => {
                let mut new_clause = CHCs.create_next_CHC();
                let head_query_params = new_clause.get_mut_head_query_params();
                head_query_params.retain(|v| v != var);
                CHCs.push(new_clause);
                Some(())
            }
            ReferenceCurrVal(name) if name == var_name => {
                drop_reference(name, CHCs, alias_groups);
                Some(())
            }
            Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_) => None,
            _ => panic!("Unexpected query parameter: {v:?}"),
        })
        .unwrap_or_else(|| {
            // We may be dropping an alias, in which case we did not find it in the query parameters
            drop_reference(var_name, CHCs, alias_groups);
        });
}

mod util {
    use crate::smtlib2;
    use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
    use crate::smtlib2::HornClause;
    use crate::smtlib2::Operation::Equals;
    use crate::syn_utils::is_borrow;
    use crate::translate::syn_expr_translation::translate_syn_expr;
    use crate::translate::utils::{AliasGroups, CHCSystem};

    #[allow(clippy::too_many_arguments)]
    pub(super) fn assign<LhsType>(
        lhs_name: &LhsType,
        rhs: &syn::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
        query_params: &[smtlib2::Expr],
        alias_groups: &mut AliasGroups,
        case_borrow: fn(&LhsType, &syn::Expr, &mut Vec<HornClause>),
        case_create_alias: fn(
            &LhsType,
            &str,
            &mut AliasGroups,
            &[smtlib2::Expr],
            &mut Vec<HornClause>,
        ),
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

        let referenced_eq_final_val =
            App(Equals, vec![referenced_var_updated.clone(), final_value]);
        new_clause.body.push(referenced_eq_final_val);
        new_clause.replace_head_query_param(&referenced_var, referenced_var_updated);
    }

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
                let new_final_val_eq_old_final_val =
                    App(Equals, vec![new_final_val, old_final_val]);
                new_clause.body.push(new_curr_val_eq_old_curr_val);
                new_clause.body.push(new_final_val_eq_old_final_val);
            }
            alias_groups.drop_alias(reference_name);
        } else {
            // if there are no aliases, then finalize the reference
            let head_query_params = new_clause.get_mut_head_query_params();
            head_query_params.retain(|v| *v != old_curr_val && *v != old_final_val);
            let final_val_eq_curr_val =
                App(Equals, vec![old_final_val.clone(), old_curr_val.clone()]);
            new_clause.body.push(final_val_eq_curr_val);
        }
        CHCs.push(new_clause);
    }
}
