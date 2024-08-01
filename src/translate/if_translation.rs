use crate::drop_elaboration::ExtendedStmt;
use crate::smtlib2::Expr::App;
use crate::smtlib2::Operation::Predicate;
use crate::smtlib2::{HornClause, Operation};
use crate::translate::syn_expr_translation::translate_syn_expr;
use crate::translate::translate_stmt;
use crate::translate::utils::CHCSystem;

pub(super) fn translate_if(
    if_stmt: &ExtendedStmt,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    if let ExtendedStmt::If(condition, then_block, else_block) = if_stmt {
        println!("If condition: {condition:?}");
        println!("Then block: {then_block:?}");
        println!("Else block: {else_block:?}");

        #[allow(non_snake_case)]
        let mut then_CHCs: Vec<HornClause> = Vec::new();
        #[allow(non_snake_case)]
        let mut else_CHCs: Vec<HornClause> = Vec::new();

        let condition = translate_syn_expr(condition);

        let mut if_clause = CHCs.create_next_CHC();
        if_clause.body.push(condition.clone());
        then_CHCs.push(if_clause);

        let mut else_clause = CHCs.create_next_CHC();
        else_clause.body.push(App(Operation::Not, vec![condition]));
        else_CHCs.push(else_clause);

        for stmt in then_block {
            translate_stmt(stmt, &mut then_CHCs);
        }

        for stmt in else_block {
            translate_stmt(stmt, &mut else_CHCs);
        }

        let last_then_query = then_CHCs
            .get_latest_query()
            .unwrap()
            .to_expr_without_trailing_apostrophes();

        let last_else_query = else_CHCs
            .get_latest_query()
            .unwrap()
            .to_expr_without_trailing_apostrophes();

        if let (App(Predicate(_), then_query_args), App(Predicate(_), else_query_args)) = (
            &last_then_query,
            &last_else_query,
        ) {
            assert_eq!(then_query_args, else_query_args);
        }

        let connecting_clause = HornClause {
            head: last_else_query,
            body: vec![last_then_query],
        };

        CHCs.append(&mut then_CHCs);
        CHCs.append(&mut else_CHCs);
        CHCs.push(connecting_clause);
    } else {
        panic!("Expected If statement, got: {if_stmt:?}");
    }
}
