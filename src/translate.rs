use syn::{Expr, Item, Stmt};

use crate::drop_elaboration::ExtendedStmt::Stmt as ExStmt;
use crate::drop_elaboration::{perform_drop_elaboration, ExtendedStmt};
use crate::smtlib2::HornClause;
use crate::syn_utils::{get_declared_var_name, is_borrow};
use crate::translate::stmt_translations::{translate_assertion, translate_drop};

mod expr_translations;
mod stmt_translations;
mod utils;

pub(crate) fn translate_item(item: &Item, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match item {
        Item::Fn(func) => {
            println!("Item::Function: {}", func.sig.ident);
            let stmts = perform_drop_elaboration(&*func.block);
            for stmt in stmts {
                translate_stmt(&stmt, CHCs);
            }
        }

        _ => {
            panic!("Unsupported item type: {:?}", item);
        }
    }
}

fn translate_stmt(stmt: &ExtendedStmt, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match stmt {
        // Borrow
        ExStmt(Stmt::Local(local)) if is_borrow(local) => {
            println!("Stmt::Local (reference): {}", get_declared_var_name(&local));
            stmt_translations::translate_borrow(local, CHCs);
        }
        // Local variable declaration
        ExStmt(Stmt::Local(local)) => {
            println!("Stmt::Local: {}", get_declared_var_name(&local));
            stmt_translations::translate_local_var_decl(local, CHCs);
        }
        ExStmt(Stmt::Expr(expr, _semicolon)) => {
            println!("Stmt::Expr");
            translate_expr(expr, CHCs);
        }
        // Assert
        ExStmt(Stmt::Macro(mac)) => {
            println!("Stmt::Macro");
            translate_assertion(mac, CHCs);
        }
        ExtendedStmt::Drop(var) => {
            println!("ExStmt::Drop: {}", var);
            translate_drop(var, CHCs);
        }

        _ => {
            panic!("Unsupported statement type: {:?}", stmt);
        }
    }
}

fn translate_expr(expr: &Expr, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match expr {
        Expr::Assign(assign) => {
            println!("Expr::Assignment");
            expr_translations::translate_assignment(assign, CHCs);
        }

        _ => {
            panic!("Unsupported expression type: {:?}", expr);
        }
    }
}
