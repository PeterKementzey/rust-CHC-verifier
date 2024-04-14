use core::panic;
use quote::quote;
use std::env;
use std::fs::File;
use std::io::Read;
use syn::parse_file;

use syn::{Expr, Item, Stmt};

mod ast_downcasters;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        println!("Please provide a file to parse");
        return;
    }

    let mut file = File::open(&args[1]).expect("Unable to open file");
    let mut src = String::new();
    file.read_to_string(&mut src).expect("Unable to read file");

    let ast = parse_file(&src).expect("Unable to parse file");

    {
        // Print program
        let tokens = quote! { #ast };
        println!("The entire AST:");
        println!("{}", tokens);
    }

    for item in ast.items {
        translate_item(item);
    }
}

fn translate_item(item: Item) {
    match item {
        Item::Fn(func) => {
            // Translate function
            println!("Function: {}", func.sig.ident);
            for stmt in func.block.stmts {
                translate_stmt(stmt);
            }
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

fn translate_stmt(stmt: Stmt) {
    match stmt {
        Stmt::Local(_local) => {
            // Translate local variable declaration
            println!("Local");
        }
        Stmt::Item(item) => {
            translate_item(item);
        }
        Stmt::Expr(expr, _semicolon) => {
            translate_expr(expr);
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

fn translate_expr(expr: Expr) {
    match expr {
        Expr::Call(_call) => {
            // Translate function call
            println!("Function call");
        }
        Expr::Binary(_bin) => {
            // Translate binary operation
            println!("Binary operation");
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
