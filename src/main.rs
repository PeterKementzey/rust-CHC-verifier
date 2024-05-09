use std::env;
use std::fs::File;
use std::io::Read;

use quote::quote;
use syn::parse_file;

mod ast_downcasters;
mod translate;

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
        translate::translate_item(item);
    }
}
