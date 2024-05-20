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

#[allow(dead_code)]
fn main2() -> Vec<HornClause> {
    // Example usage
    let x = Expr::var("x");
    let y = Expr::var("y");
    let z = Expr::var("z");

    let expr1 = Expr::App(Operation::GreaterThan, vec![x.clone(), Expr::Const(0)]);
    let expr2 = Expr::App(Operation::LessThan, vec![y.clone(), Expr::Const(10)]);
    let head1 = Expr::App(
        Operation::predicate("p"),
        vec![x.clone(), y.clone(), z.clone()],
    );
    let body1 = vec![expr1, expr2];

    let clause1 = HornClause {
        head: head1,
        body: body1,
    };

    let expr3 = Expr::App(Operation::Equals, vec![z.clone(), Expr::Const(5)]);
    let head2 = Expr::App(Operation::predicate("q"), vec![z.clone()]);
    let body2 = vec![expr3];

    let clause2 = HornClause {
        head: head2,
        body: body2,
    };

    let clauses = vec![clause1, clause2];
    return clauses;
}

#[allow(dead_code)]
fn example_clauses() -> Vec<HornClause> {
    #[allow(non_snake_case)]
    let mut CHCs: Vec<HornClause> = Vec::new();
    CHCs.push(HornClause {
        head: Expr::App(
            Operation::predicate("q1"),
            vec![Expr::var("x"),],
        ),
        body: vec![
            Expr::App(Operation::Equals, vec![Expr::var("x"), Expr::Const(42)]),
        ],
    });
    CHCs.push(HornClause {
        head: Expr::App(
            Operation::predicate("q2"),
            vec![Expr::var("y*"),
            Expr::var("y^"),
            Expr::var("x^")],
        ),
        body: vec![
            Expr::App(Operation::predicate("q1"), vec![Expr::var("x")]),
            Expr::App(Operation::Equals, vec![Expr::var("y*"), Expr::var("x")]),
            Expr::App(Operation::Equals, vec![Expr::var("x^"), Expr::var("y^")]),
        ],
    });
    CHCs.push(HornClause {
        head: Expr::App(
            Operation::predicate("q3"),
            vec![Expr::var("y^^"), Expr::var("y^"), Expr::var("x")],
        ),
        body: vec![
            Expr::App(Operation::predicate("q2"), vec![Expr::var("y*"), Expr::var("y^"), Expr::var("x")]),
            Expr::App(Operation::Equals, vec![Expr::var("y^^"), Expr::App(Operation::Plus, vec![Expr::var("y*"), Expr::Const(1)])]),
        ],
    });
    CHCs.push(HornClause {
        head: Expr::App(
            Operation::predicate("q4"),
            vec![Expr::var("x")],
        ),
        body: vec![
            Expr::App(Operation::predicate("q3"), vec![Expr::var("y*"), Expr::var("y^"), Expr::var("x")]),
            Expr::App(Operation::Equals, vec![Expr::var("y^"), Expr::var("y*")]),
        ],
    });
    CHCs.push(HornClause {
        head: Expr::App(
            Operation::Equals,
            vec![Expr::var("x"), Expr::Const(43)],
        ),
        body: vec![
            Expr::App(Operation::predicate("q4"), vec![Expr::var("x")]),
        ],
    });
    
    return CHCs;
}

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
        // TODO
        translate::translate_item(&item, &mut CHCs);
    }

    // CHCs = example_clauses(); // FIXME remove this line

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
