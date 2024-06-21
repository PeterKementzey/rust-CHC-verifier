use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::Equals;
use crate::syn_utils::{
    get_assert_condition, get_borrowed_name, get_declared_var_name, get_macro_name,
};
use crate::translate::borrow_utils;
use crate::translate::borrow_utils::{borrow_variable, drop_reference};
use crate::translate::expr_translations::translate_syn_expr;
use crate::translate::utils::{AliasGroups, CHCSystem};
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
        reference_name: &String,
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
        #[allow(non_snake_case)] _CHCs: &mut Vec<HornClause>,
    ) {
        alias_groups.add_alias(rhs_name.to_string(), new_alias_name.to_string());
    }

    fn case_integer_init(
        new_var_name: &String,
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

    borrow_utils::translate_assignment(
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

pub(super) fn translate_assertion(
    stmt_macro: &syn::StmtMacro,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    alias_groups: &AliasGroups,
) {
    let macro_name = get_macro_name(stmt_macro);
    assert_eq!(macro_name, "assert", "Unsupported macro name: {macro_name}");

    let condition: syn::Expr = get_assert_condition(stmt_macro);
    let condition: smtlib2::Expr = translate_syn_expr(&condition, alias_groups);

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
