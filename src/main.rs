use std::env;
use std::fs::File;
use std::io::Read;

use quote::quote;
use syn::parse_file;

use smtlib2::HornClause;

use crate::smtlib2::Smtlib2Display;

mod drop_elaboration;
mod smtlib2;
mod syn_utils;
mod translate;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        println!("Please provide a single file to parse");
        return;
    }
    if !args[1].ends_with(".rs") {
        println!("Please provide a Rust file (.rs)");
        return;
    }

    let src = {
        let mut source_file = File::open(&args[1]).expect("Unable to open file");
        let mut src = String::new();
        source_file
            .read_to_string(&mut src)
            .expect("Unable to read file");
        src
    };

    let ast = parse_file(&src).expect("Unable to parse file");

    {
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

    let smt2_file_name = format!("{}.smt2", &args[1][..args[1].len() - 3]);
    let smt2_file = File::create(&smt2_file_name);

    let output: Box<dyn Write> = match smt2_file {
        Ok(file) => {
            println!("Writing to file: {}", smt2_file_name);
            Box::new(file)
        }
        Err(e) => {
            println!("Could not open/create smt2 file: {}", e);
            println!("Writing to standard output:");
            Box::new(stdout())
        }
    };

    CHCs.write_as_smtlib2(output)
        .expect("Could not write to output");
}
