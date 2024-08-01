use syn::ExprAssign;

use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
use crate::smtlib2::HornClause;
use crate::smtlib2::Operation::Equals;
use crate::syn_utils::{get_borrowed_name, get_declared_var_name};
use crate::translate::syn_expr_translation::translate_syn_expr;
use crate::translate::utils::CHCSystem;
use crate::translate::var_translations::util::{assign, create_reference};
use crate::{smtlib2, syn_utils};

///  Local variable initialization can be one of the following:
///  - If the new variable is a reference then
///     - Either we are newly borrowing a variable
///     - Or we are creating a new alias from another reference variable
///  - If the new variable is an integer then it's just an assignment initialization
pub(super) fn translate_local_var_decl(
    local: &syn::Local,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    #[allow(clippy::similar_names)]
    pub(super) fn case_borrow(
        #[allow(clippy::ptr_arg)] reference_name: &String,
        rhs: &syn::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let referenced_name = get_borrowed_name(rhs);
        let referenced_var = Var(referenced_name);

        create_reference(reference_name, &referenced_var, CHCs);
    }

    pub(super) fn case_create_alias(
        #[allow(clippy::ptr_arg)] new_alias_name: &String,
        rhs_name: &str,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let referenced_ref = ReferenceCurrVal(rhs_name.to_string());

        create_reference(new_alias_name, &referenced_ref, CHCs);
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

    let new_var_name = get_declared_var_name(local);
    let initial_value = syn_utils::get_init_expr(local).expect("Local variable not initialized");

    let query_params: Vec<smtlib2::Expr> = CHCs
        .get_latest_query()
        .into_iter()
        .flat_map(|q| q.get_stripped_query_params())
        .collect();

    assign(
        &new_var_name,
        initial_value,
        CHCs,
        &query_params,
        case_borrow,
        case_create_alias,
        case_integer_init,
    );
}

pub(super) fn translate_assignment(
    assignment: &ExprAssign,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    fn get_reference_name(lhs: &smtlib2::Expr) -> String {
        // if we are creating an alias then from syntax lhs seems like a `Var`, but is actually a `ReferenceCurrVal`
        match &lhs {
            Var(name) => name.clone(),
            _ => panic!("Left hand side is not a variable"),
        }
    }

    fn case_borrow(
        lhs: &smtlib2::Expr,
        rhs: &syn::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let lhs_name = get_reference_name(lhs);
        let referenced_name = get_borrowed_name(rhs);
        let referenced_var = Var(referenced_name.clone());
        create_reference(&lhs_name, &referenced_var, CHCs);
    }

    fn case_create_alias(
        lhs: &smtlib2::Expr,
        rhs_name: &str,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let lhs_name = get_reference_name(lhs);
        let referenced_ref = ReferenceCurrVal(rhs_name.to_string());

        create_reference(&lhs_name, &referenced_ref, CHCs);
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
        new_clause.replace_head_query_param(lhs, updated_lhs.clone());

        let assignment = App(Equals, vec![updated_lhs, rhs]);
        new_clause.body.push(assignment);

        CHCs.push(new_clause);
    }

    assert!(!CHCs.is_empty(), "Assignment reached with no CHCs");

    let lhs: smtlib2::Expr = translate_syn_expr(&assignment.left);
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
        case_borrow,
        case_create_alias,
        case_integer_assign,
    );
}

pub(super) fn translate_drop(
    var_name: &String,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
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
            ReferenceCurrVal(reference_name) if reference_name == var_name => {
                let mut new_clause = CHCs.create_next_CHC();
                let curr_val = ReferenceCurrVal(reference_name.clone());
                let final_val = ReferenceFinalVal(reference_name.clone());
                let head_query_params = new_clause.get_mut_head_query_params();
                head_query_params.retain(|v| *v != curr_val && *v != final_val);
                let final_val_eq_curr_val = App(Equals, vec![final_val.clone(), curr_val.clone()]);
                new_clause.body.push(final_val_eq_curr_val);
                CHCs.push(new_clause);
                Some(())
            }
            Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_) => None,
            _ => panic!("Unexpected query parameter: {v:?}"),
        })
        .expect("Variable to drop not found in query parameters");
}

pub(super) fn translate_last_use_before_overwrite(
    var_name: &String,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let query_params = CHCs
        .get_latest_query()
        .expect("No queries to drop reference from")
        .get_stripped_query_params();

    query_params
        .iter()
        .find_map(|v| match v {
            Var(name) if name == var_name => Some(()),
            ReferenceCurrVal(reference_name) if reference_name == var_name => {
                translate_drop(reference_name, CHCs);
                Some(())
            }
            Var(_) | ReferenceCurrVal(_) | ReferenceFinalVal(_) => None,
            _ => panic!("Unexpected query parameter: {v:?}"),
        })
        .expect("Variable to drop not found in query parameters");
}

mod util {
    use crate::smtlib2;
    use crate::smtlib2::Expr::{App, ReferenceCurrVal, ReferenceFinalVal, Var};
    use crate::smtlib2::HornClause;
    use crate::smtlib2::Operation::Equals;
    use crate::syn_utils::is_borrow;
    use crate::translate::syn_expr_translation::translate_syn_expr;
    use crate::translate::utils::CHCSystem;

    /// - There are 2 functions:
    ///   - Variable declaration
    ///   - Assignment
    /// - Variable declaration:
    ///   - (No initialization - disallowed for now (or forever))
    ///   - Simple assignment (integer)
    ///   - Assignment of other borrow (alias creation)
    ///     - We know this from the fact that rhs is a reference
    ///   - Borrow of variable (could be that there is already a borrow to this variable in which case also alias)
    ///     - We know this from syntax
    /// - Assignment
    ///   - Simple assignment (integer)
    ///   - Assignment of other borrow (alias creation)
    ///     - We know this from both left and right being a reference
    ///   - Borrow of variable (could be that there is already a borrow to this variable in which case also alias)
    ///     - We know this from syntax
    ///
    /// We start with checking in syntax if it's a borrow. If not we can parse the rhs. Then we check if rhs is a reference.
    /// If it is, it means we are creating an alias. If it's not, we are doing an integer assignment.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn assign<LhsType>(
        lhs: &LhsType,
        rhs: &syn::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
        query_params: &[smtlib2::Expr],
        case_borrow: fn(&LhsType, &syn::Expr, &mut Vec<HornClause>),
        case_create_alias: fn(&LhsType, &str, &mut Vec<HornClause>),
        case_integer_assign: fn(&LhsType, smtlib2::Expr, &mut Vec<HornClause>),
    ) {
        if is_borrow(rhs) {
            // option 1: borrow - we know this from syntax
            case_borrow(lhs, rhs, CHCs);
        } else {
            let rhs: smtlib2::Expr = translate_syn_expr(rhs);

            match rhs {
                // if we are creating an alias then from syntax rhs seems like a `Var`, but is actually a `ReferenceCurrVal`
                Var(rhs_name) if { query_params.contains(&ReferenceCurrVal(rhs_name.clone())) } => {
                    // option 2: create alias - we know from query params whether rhs is a reference
                    case_create_alias(lhs, &rhs_name, CHCs);
                }

                // option 3: integer assignment - if neither of the above
                _ => case_integer_assign(lhs, rhs, CHCs),
            }
        }
    }

    #[allow(clippy::similar_names)]
    /// Assumes reference (curr & final) is already present in head query params
    pub(super) fn create_reference(
        reference_name: &str,
        referenced_expr: &smtlib2::Expr,
        #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
    ) {
        let current_value = ReferenceCurrVal(reference_name.to_string());
        let final_value = ReferenceFinalVal(reference_name.to_string());
        let referenced_expr_updated = match referenced_expr.clone() {
            Var(name) => Var(name + "'"),
            ReferenceCurrVal(name) => ReferenceCurrVal(name + "'"),
            _ => panic!("Illegal referenced expression"),
        };

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
            new_clause.head_contains(referenced_expr),
            "Referenced variable not found in latest query"
        );
        assert!(
            !new_clause.head_contains(&referenced_expr_updated),
            "Referenced variable updated already present in query parameters"
        );

        new_clause.insert_head_query_param(current_value.clone());
        new_clause.insert_head_query_param(final_value.clone());
        new_clause.replace_head_query_param(referenced_expr, referenced_expr_updated.clone());

        let curr_val_eq_referenced = App(Equals, vec![current_value, referenced_expr.clone()]);
        new_clause.body.push(curr_val_eq_referenced);

        let referenced_eq_final_val = App(Equals, vec![referenced_expr_updated, final_value]);
        new_clause.body.push(referenced_eq_final_val);

        CHCs.push(new_clause);
    }
}
