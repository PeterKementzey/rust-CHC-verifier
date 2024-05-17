use std::env;
use std::fs::File;
use std::io::Read;

use quote::quote;
use syn::parse_file;

use smtlib2::{
    Expr, extract_unique_predicates, generate_predicate_declarations, HornClause, Operation,
};

mod ast_downcasters;
mod smtlib2;
mod translate;

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

    let mut CHCs: Vec<HornClause> = Vec::new();
    for item in ast.items {
        // TODO
        CHCs = translate::translate_item(&item);
    }

    let unique_predicates = extract_unique_predicates(&CHCs);
    let predicate_declarations = generate_predicate_declarations(&unique_predicates);

    {
        use std::io::{stdout, Write};

        let smt2_file = File::create(format!("{}.smt2", &args[1][..args[1].len() - 3]));

        let mut output: Box<dyn Write> = match smt2_file {
            Ok(file) => Box::new(file),
            Err(e) => {
                println!("Could not open/create smt2 file: {}", e);
                println!("Writing to standard output:");
                Box::new(stdout())
            }
        };

        writeln!(output, "(set-logic HORN)").expect("Unable to write to file");

        for decl in &predicate_declarations {
            writeln!(output, "{}", decl).expect("Unable to write to file");
        }

        for clause in &CHCs {
            writeln!(output, "{}", clause).expect("Unable to write to file");
        }

        writeln!(output, "(check-sat)").expect("Unable to write to file");
        writeln!(output, "(get-model)").expect("Unable to write to file");
    }
}
