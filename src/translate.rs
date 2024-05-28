use syn::{Block, Expr, Item, Stmt};

use crate::smtlib2::HornClause;
use crate::translate::stmt_translations::translate_assertion;

mod expr_translations;
mod stmt_translations;
mod utils;

pub(crate) fn translate_item(item: &Item, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match item {
        Item::Fn(func) => {
            // Translate function
            println!("Item::Function: {}", func.sig.ident);
            translate_block(&*func.block, CHCs);
        }
        // Add more cases as needed
        _ => {
            panic!("Unsupported item type: {:?}", item);
        }
    }
}

fn translate_stmt(stmt: &Stmt, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match stmt {
        Stmt::Local(local) => {
            // Translate local variable declaration
            println!("Stmt::Local");
            stmt_translations::translate_local_var_decl(local, CHCs);
        }
        // Stmt::Item(item) => {
        //     println!("Stmt::Item");
        //     translate_item(item);
        // }
        Stmt::Expr(expr, _semicolon) => {
            println!("Stmt::Expr");
            translate_expr(expr, CHCs);
        }
        Stmt::Macro(mac) => {
            // Translate macro
            println!("Stmt::Macro");
            translate_assertion(mac, CHCs);
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
        Expr::Block(block) => {
            // Translate block
            println!("Expr::Block");
            translate_block(&block.block, CHCs)
        }
        Expr::Assign(assign) => {
            // Translate assignment
            println!("Expr::Assignment");
            println!("Assignment: {:?}", assign);
            expr_translations::translate_assignment(assign, CHCs);
        }
        // Add more cases as needed
        _ => {
            panic!("Unsupported expression type: {:?}", expr);
        }
    }
}

fn translate_block(block: &Block, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    for stmt in &block.stmts {
        translate_stmt(stmt, CHCs);
    }
}
