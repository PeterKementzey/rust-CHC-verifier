use std::env;
use std::fs;
use std::fs::File;
use std::io::{stdout, Write};
use std::path::{Path, PathBuf};

use log::{log_enabled, trace, Level};
use quote::quote;
use syn::parse_file;

use smtlib2::HornClause;

use crate::smtlib2::Smtlib2Display;

mod drop_elaboration;
mod smtlib2;
mod syn_utils;
mod translate;

fn main() {
    setup_logging();

    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Please provide a single file to parse");
        return;
    }
    let source_path = Path::new(&args[1]);
    if !source_path
        .extension()
        .map_or(false, |ext| ext.eq_ignore_ascii_case("rs"))
    {
        eprintln!("Please provide a Rust file (.rs)");
        return;
    }

    let src = fs::read_to_string(source_path).expect("Unable to read file");
    let ast = parse_file(&src).expect("Unable to parse file");

    if log_enabled!(Level::Trace) {
        let tokens = quote! { #ast };
        trace!("The entire AST:");
        trace!("{tokens}");
    }

    #[allow(non_snake_case)]
    let mut CHCs: Vec<HornClause> = Vec::new();
    for item in ast.items {
        translate::translate_item(&item, &mut CHCs);
    }

    let smt2_file_path = {
        let mut path = PathBuf::from(source_path);
        path.set_extension("smt2");
        path
    };
    let smt2_file = File::create(&smt2_file_path);

    let output: Box<dyn Write> = match smt2_file {
        Ok(file) => {
            println!("Writing to file: {}", smt2_file_path.display());
            Box::new(file)
        }
        Err(e) => {
            eprintln!("Could not open/create smt2 file: {e}");
            println!("Writing to standard output:");
            Box::new(stdout())
        }
    };

    CHCs.write_as_smtlib2(output)
        .expect("Could not write to output");
}

fn setup_logging() {
    env_logger::builder()
        .format(|buf, record| {
            let level = match record.level() {
                Level::Error => "\x1b[31mERROR\x1b[0m", // Red
                Level::Warn => "\x1b[33mWARN\x1b[0m",   // Yellow
                Level::Info => "\x1b[32mINFO\x1b[0m",   // Green
                Level::Debug => "\x1b[34mDEBUG\x1b[0m", // Blue
                Level::Trace => "\x1b[94mTRACE\x1b[0m", // Light Blue
            };
            writeln!(buf, "{}: {}", level, record.args())
        })
        .init();
}
