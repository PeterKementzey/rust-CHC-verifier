use std::env;
use std::fs::File;
use std::io::Read;

use quote::quote;
use syn::parse_file;

use smtlib2::HornClause;

use crate::smtlib2::Smtlib2Display;

mod smtlib2;
mod translate;
mod syn_utils;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        println!("Please provide a file to parse");
        return;
    }
    if !args[1].ends_with(".rs") {
        println!("Please provide a Rust file (.rs)");
        return;
    }

    let mut src = String::new();
    {
        let mut source_file = File::open(&args[1]).expect("Unable to open file");
        source_file
            .read_to_string(&mut src)
            .expect("Unable to read file");
    }

    let ast = parse_file(&src).expect("Unable to parse file");

    {
        // FIXME remove this block
        // Print program
        let tokens = quote! { #ast };
        println!("The entire AST:");
        println!("{}", tokens);
    }

    #[allow(non_snake_case)]
    let mut CHCs: Vec<HornClause> = Vec::new();
    for item in ast.items {
        translate::translate_item(&item, &mut CHCs);
    }

    use std::io::{stdout, Write};

    let smt2_file = File::create(format!("{}.smt2", &args[1][..args[1].len() - 3]));

    let output: Box<dyn Write> = match smt2_file {
        Ok(file) => Box::new(file),
        Err(e) => {
            println!("Could not open/create smt2 file: {}", e);
            println!("Writing to standard output:");
            Box::new(stdout())
        }
    };

    CHCs.write_as_smtlib2(output)
        .expect("Could not write to output");
}
