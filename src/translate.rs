use syn::{Block, Expr, Item, Stmt};

use crate::ast_downcasters;
use crate::smtlib2::HornClause;

mod stmt_translations;
pub(crate) mod utils;

pub(crate) fn translate_item(item: &Item, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match item {
        Item::Fn(func) => {
            // Translate function
            println!("Item::Function: {}", func.sig.ident);
            translate_block(&*func.block, CHCs);
        }
        // Add more cases as needed
        _ => {
            panic!(
                "Unsupported item type: {}",
                ast_downcasters::downcast_item(item)
            );
        }
    }
}

fn translate_stmt(stmt: &Stmt, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    match stmt {
        Stmt::Local(local) => {
            // Translate local variable declaration
            println!("Stmt::Local");
            println!("Local variable: {:?}", local);
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
        Stmt::Macro(_mac) => {
            // Translate macro
            println!("Stmt::Macro");
        }
        // Add more cases as needed
        _ => {
            panic!(
                "Unsupported statement type: {}",
                ast_downcasters::downcast_statement(stmt)
            );
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
        Expr::Assign(_assign) => {
            // Translate assignment
            println!("Expr::Assignment");
        }
        // Add more cases as needed
        _ => {
            panic!(
                "Unsupported expression type: {}",
                ast_downcasters::downcast_expression(expr)
            );
        }
    }
}

fn translate_block(block: &Block, #[allow(non_snake_case)] CHCs: &mut Vec<HornClause>) {
    for stmt in &block.stmts {
        translate_stmt(stmt, CHCs);
    }
}
