use log::trace;
use syn::{Expr, Item, Stmt};

use crate::drop_elaboration::ExtendedStmt::Stmt as ExStmt;
use crate::drop_elaboration::{perform_drop_elaboration, ExtendedStmt};
use crate::smtlib2::HornClause;
use crate::syn_utils::get_declared_var_name;
use crate::translate::assert_translation::translate_assertion;
use crate::translate::if_translation::translate_if;
use crate::translate::var_translations::{
    translate_assignment, translate_drop, translate_last_use_before_overwrite,
    translate_local_var_decl,
};

mod assert_translation;
mod if_translation;
mod syn_expr_translation;
mod utils;
mod var_translations;

pub(crate) fn translate_item(item: &Item, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match item {
        Item::Fn(func) => {
            trace!("Item::Function: {}", func.sig.ident);
            let stmts = perform_drop_elaboration(&func.block);
            for stmt in stmts {
                translate_stmt(&stmt, CHCs);
            }
        }

        _ => {
            panic!("Unsupported item type: {item:?}");
        }
    }
}

fn translate_stmt(stmt: &ExtendedStmt, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    #[allow(clippy::match_wildcard_for_single_variants)]
    match stmt {
        // Local variable declaration
        ExStmt(Stmt::Local(local)) => {
            trace!("Stmt::Local: {}", get_declared_var_name(local));
            translate_local_var_decl(local, CHCs);
        }
        ExStmt(Stmt::Expr(expr, _semicolon)) => {
            trace!("Stmt::Expr");
            translate_expr(expr, CHCs);
        }
        // Assert
        ExStmt(Stmt::Macro(mac)) => {
            trace!("Stmt::Macro");
            translate_assertion(mac, CHCs);
        }
        ExtendedStmt::Drop(var) => {
            trace!("ExStmt::Drop: {var}");
            translate_drop(var, CHCs);
        }
        ExtendedStmt::LastUseBeforeOverwrite(var) => {
            trace!("ExStmt::LastUseBeforeOverwrite: {var}");
            translate_last_use_before_overwrite(var, CHCs);
        }
        if_stmt @ ExtendedStmt::If(_, _, _) => {
            trace!("ExStmt::If");
            translate_if(if_stmt, CHCs);
        }

        _ => {
            panic!("Unsupported statement type: {stmt:?}");
        }
    }
}

fn translate_expr(expr: &Expr, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match expr {
        Expr::Assign(assign) => {
            trace!("Expr::Assignment");
            translate_assignment(assign, CHCs);
        }

        _ => {
            panic!("Unsupported expression type: {expr:?}");
        }
    }
}
