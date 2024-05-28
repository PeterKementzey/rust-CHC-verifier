use syn::{Expr, Item, Stmt};

use crate::drop_elaboration::ExtendedStmt::Stmt as ExStmt;
use crate::drop_elaboration::{perform_drop_elaboration, ExtendedStmt};
use crate::smtlib2::HornClause;
use crate::syn_utils::get_local_var_name;
use crate::translate::stmt_translations::translate_assertion;

mod expr_translations;
mod stmt_translations;
mod utils;

pub(crate) fn translate_item(item: &Item, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match item {
        Item::Fn(func) => {
            // Translate function
            println!("Item::Function: {}", func.sig.ident);
            let stmts = perform_drop_elaboration(&*func.block);
            for stmt in stmts {
                translate_stmt(&stmt, CHCs);
            }
        }
        // Add more cases as needed
        _ => {
            panic!("Unsupported item type: {:?}", item);
        }
    }
}

fn translate_stmt(stmt: &ExtendedStmt, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match stmt {
        ExStmt(Stmt::Local(local)) => {
            // Translate local variable declaration
            println!("Stmt::Local: {}", get_local_var_name(&local));
            stmt_translations::translate_local_var_decl(local, CHCs);
        }
        // Stmt::Item(item) => {
        //     println!("Stmt::Item");
        //     translate_item(item);
        // }
        ExStmt(Stmt::Expr(expr, _semicolon)) => {
            println!("Stmt::Expr");
            translate_expr(expr, CHCs);
        }
        ExStmt(Stmt::Macro(mac)) => {
            // Translate macro
            println!("Stmt::Macro");
            translate_assertion(mac, CHCs);
        }
        ExtendedStmt::Drop(var) => {
            // Drop
            println!("ExStmt::Drop: {}", var);
        }
        // Add more cases as needed
        _ => {
            panic!("Unsupported statement type: {:?}", stmt);
        }
    }
}

fn translate_expr(expr: &Expr, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match expr {
        // Expr::Call(_call) => {
        //     // Translate function call
        //     println!("Expr::Function call");
        // }
        // Expr::Binary(_bin) => {
        //     // Translate binary operation
        //     println!("Expr::Binary operation");
        // }
        // Expr::Block(block) => {
        //     panic!("Nested blocks are not supported because drop elaboration does not handle them.");
        //     // Translate block
        //     println!("Expr::Block");
        // }
        Expr::Assign(assign) => {
            // Translate assignment
            println!("Expr::Assignment");
            expr_translations::translate_assignment(assign, CHCs);
        }
        // Add more cases as needed
        _ => {
            panic!("Unsupported expression type: {:?}", expr);
        }
    }
}
