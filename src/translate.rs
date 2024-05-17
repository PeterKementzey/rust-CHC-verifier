use syn::{Block, Expr, Item, Stmt};

use crate::ast_downcasters;
use crate::smtlib2::HornClause;

pub(crate) fn translate_item(item: &Item) -> Vec<HornClause> {
    match item {
        Item::Fn(func) => {
            // Translate function
            println!("Function: {}", func.sig.ident);
            translate_block(&*func.block);
            Vec::new()
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

fn translate_stmt(stmt: &Stmt) {
    match stmt {
        Stmt::Local(_local) => {
            // Translate local variable declaration
            println!("Local");
        }
        // Stmt::Item(item) => {
        //     translate_item(item);
        // }
        Stmt::Expr(expr, _semicolon) => {
            translate_expr(expr);
        }
        Stmt::Macro(_mac) => {
            // Translate macro
            println!("Macro");
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

fn translate_expr(expr: &Expr) {
    match expr {
        // Expr::Call(_call) => {
        //     // Translate function call
        //     println!("Function call");
        // }
        // Expr::Binary(_bin) => {
        //     // Translate binary operation
        //     println!("Binary operation");
        // }
        Expr::Block(block) => {
            // Translate block
            println!("Block");
            translate_block(&block.block)
        }
        Expr::Assign(_assign) => {
            // Translate assignment
            println!("Assignment");
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

fn translate_block(block: &Block) {
    for stmt in &block.stmts {
        translate_stmt(stmt);
    }
}
