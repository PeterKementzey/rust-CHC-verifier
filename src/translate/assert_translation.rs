use crate::smtlib2;
use crate::smtlib2::HornClause;
use crate::syn_utils::{get_assert_condition, get_macro_name};
use crate::translate::syn_expr_translation::translate_syn_expr;
use crate::translate::utils::CHCSystem;

pub(super) fn translate_assertion(
    stmt_macro: &syn::StmtMacro,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    let macro_name = get_macro_name(stmt_macro);
    assert_eq!(macro_name, "assert", "Unsupported macro name: {macro_name}");

    let condition: syn::Expr = get_assert_condition(stmt_macro);
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
