use crate::drop_elaboration::ExtendedStmt;
use crate::smtlib2::{Expr, HornClause, Operation};
use crate::translate::syn_expr_translation::translate_syn_expr;
use crate::translate::translate_stmt;
use crate::translate::utils::CHCSystem;

pub(super) fn translate_if(
    if_stmt: &ExtendedStmt,
    #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>,
) {
    if let ExtendedStmt::If(condition, then_block, else_block) = if_stmt {
        // note: at the end of the if block if all goes well then both queries should have the exact same parameters, same variables were dropped
        // you should assert this. don't forget about possibility of aliases - but also the two alias_groups should be equivalent
        println!("If condition: {condition:?}");
        println!("Then block: {then_block:?}");
        println!("Else block: {:?}", else_block.as_ref().unwrap());

        #[allow(non_snake_case)]
        let mut then_CHCs: Vec<HornClause> = Vec::new();
        #[allow(non_snake_case)]
        let mut else_CHCs: Vec<HornClause> = Vec::new();
        // let mut then_alias_groups = alias_groups.clone(); // TODO

        let condition = translate_syn_expr(condition);

        let mut if_clause = CHCs.create_next_CHC();
        if_clause.body.push(condition.clone());
        then_CHCs.push(if_clause);

        let mut else_clause = CHCs.create_next_CHC();
        else_clause
            .body
            .push(Expr::App(Operation::Not, vec![condition]));
        else_CHCs.push(else_clause);

        for stmt in then_block {
            translate_stmt(stmt, &mut then_CHCs);
        }

        // TODO else

        let last_then_query = then_CHCs
            .get_latest_query()
            .unwrap()
            .to_expr_without_trailing_apostrophes();

        CHCs.append(&mut then_CHCs);
        CHCs.append(&mut else_CHCs);

        // TODO check that the last query of else block is equal to the last query of the else block

        let connecting_clause_else = CHCs.create_next_CHC();
        let connecting_clause_then = {
            let mut clause = connecting_clause_else.clone();
            clause.body = vec![last_then_query];
            clause
        };

        CHCs.push(connecting_clause_then);
        CHCs.push(connecting_clause_else);
    } else {
        panic!("Expected If statement, got: {if_stmt:?}");
    }
}
