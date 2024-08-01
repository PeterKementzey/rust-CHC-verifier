use std::collections::HashSet;

use itertools::Itertools;
use syn::Stmt;
use syn::{visit::Visit, Block, Expr, ExprAssign};

use crate::syn_utils;

use self::util::{DeclaredVarCollector, VarCollector};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ExtendedStmt {
    Stmt(Stmt),
    Drop(String),
    LastUseBeforeOverwrite(String),
    If(Expr, Vec<ExtendedStmt>, Vec<ExtendedStmt>),
}

fn find_last_used_and_overwritten_vars_in_stmt<T>(
    stmt: &ExtendedStmt,
    variables_to_drop: &HashSet<String>,
    overwritten_variables: &HashSet<String>,
) -> (T, T)
where
    T: FromIterator<String>,
{
    let mut collector = VarCollector::new();
    collector.visit_extended_stmt(stmt);

    let last_used_vars: T = collector
        .variables
        .iter()
        .filter(|var| variables_to_drop.contains(*var))
        .sorted()
        .cloned()
        .collect();

    let last_used_before_overwrite: T = collector
        .variables
        .iter()
        .filter(|var| overwritten_variables.contains(*var))
        .sorted()
        .cloned()
        .collect();

    (last_used_vars, last_used_before_overwrite)
}

fn add_drops_to_block(
    stmts: &mut Vec<ExtendedStmt>,
    variables_to_drop: &mut HashSet<String>,
    overwritten_variables: &mut HashSet<String>,
) {
    for i in (0..stmts.len()).rev() {
        match &mut stmts[i] {
            ref ex_stmt @ ExtendedStmt::Stmt(ref stmt) => {
                let (last_used_vars, last_used_before_overwrite): (Vec<String>, Vec<String>) =
                    find_last_used_and_overwritten_vars_in_stmt(
                        ex_stmt,
                        variables_to_drop,
                        overwritten_variables,
                    );

                // need to remove first, then add, as we may need to readd
                overwritten_variables.retain(|var| !last_used_before_overwrite.contains(var));

                // in lexical lifetimes if a reference is overwritten,
                // then the reference should be dropped after the previous use
                if let Stmt::Expr(Expr::Assign(ExprAssign { left, .. }), _semicolon) = stmt {
                    if let Expr::Path(path) = left.as_ref() {
                        let var_name = syn_utils::get_var_name(path);
                        overwritten_variables.insert(var_name);
                    }
                }

                for var in last_used_before_overwrite.iter().rev() {
                    stmts.insert(i + 1, ExtendedStmt::LastUseBeforeOverwrite(var.clone()));
                }

                for var in last_used_vars.iter().rev() {
                    stmts.insert(i + 1, ExtendedStmt::Drop(var.clone()));
                    variables_to_drop.remove(var);
                }
            }
            if_stmt @ ExtendedStmt::If(_, _, _) => {
                let (mut last_used_vars, mut last_used_before_overwrite): (
                    HashSet<String>,
                    HashSet<String>,
                ) = find_last_used_and_overwritten_vars_in_stmt(
                    if_stmt,
                    variables_to_drop,
                    overwritten_variables,
                );

                variables_to_drop.retain(|var| !last_used_vars.contains(var));
                overwritten_variables.retain(|var| !last_used_before_overwrite.contains(var));

                if let ExtendedStmt::If(_, then_block, else_block) = if_stmt {
                    add_drops_to_if_branch(
                        then_block,
                        &mut last_used_vars.clone(),
                        &mut last_used_before_overwrite.clone(),
                    );
                    add_drops_to_if_branch(
                        else_block,
                        &mut last_used_vars,
                        &mut last_used_before_overwrite,
                    );
                } else {
                    unreachable!()
                }

                #[allow(clippy::items_after_statements)]
                fn add_drops_to_if_branch(
                    branch_stmts: &mut Vec<ExtendedStmt>,
                    last_used_vars: &mut HashSet<String>,
                    last_used_before_overwrite: &mut HashSet<String>,
                ) {
                    let locally_declared_vars: HashSet<String> = {
                        let mut collector = DeclaredVarCollector::new();
                        collector.visit_extended_stmt_block(branch_stmts);
                        collector.variables
                    };
                    last_used_vars.extend(locally_declared_vars.iter().cloned());
                    add_drops_to_block(branch_stmts, last_used_vars, last_used_before_overwrite);
                    let remaining_vars: Vec<String> =
                        last_used_vars.iter().sorted().cloned().collect();
                    let remaining_overwritten_vars: Vec<String> = last_used_before_overwrite
                        .iter()
                        .sorted()
                        .cloned()
                        .collect();
                    for var in remaining_overwritten_vars.iter().rev() {
                        branch_stmts.insert(0, ExtendedStmt::LastUseBeforeOverwrite(var.clone()));
                    }
                    for var in remaining_vars.iter().rev() {
                        branch_stmts.insert(0, ExtendedStmt::Drop(var.clone()));
                    }
                }
            }
            ExtendedStmt::Drop(var) | ExtendedStmt::LastUseBeforeOverwrite(var) => {
                panic!("Drop/LastUseBeforeOverwrite statement in drop elaboration: {var}")
            }
        }
    }
}

pub(crate) fn perform_drop_elaboration(block: &Block) -> Vec<ExtendedStmt> {
    let mut variables_to_drop: HashSet<String> = {
        let mut collector = DeclaredVarCollector::new();
        collector.visit_block(block);
        collector.variables
    };
    let mut overwritten_variables: HashSet<String> = HashSet::new();

    let mut extended_stmts: Vec<ExtendedStmt> = ExtendedStmt::from_block(block);

    add_drops_to_block(
        &mut extended_stmts,
        &mut variables_to_drop,
        &mut overwritten_variables,
    );

    assert!(
        variables_to_drop.is_empty(),
        "Variables not dropped: {variables_to_drop:?}"
    );
    assert!(
        overwritten_variables.is_empty(),
        "Variables not overwritten: {overwritten_variables:?}"
    );

    extended_stmts
}

mod util {
    use std::collections::HashSet;

    use syn::visit::Visit;
    use syn::{Block, Expr, ExprIf, Ident, Local, Stmt, StmtMacro};

    use crate::drop_elaboration::ExtendedStmt;
    use crate::syn_utils;

    impl ExtendedStmt {
        fn from(stmt: Stmt) -> Self {
            if let Stmt::Expr(Expr::If(if_expr), _) = &stmt {
                let condition = if_expr.cond.as_ref().clone();
                let then_block = ExtendedStmt::from_block(&if_expr.then_branch);
                let else_block = match syn_utils::get_else_block(if_expr) {
                    Some(else_block) => ExtendedStmt::from_block(else_block),
                    None => Vec::new(),
                };

                ExtendedStmt::If(condition, then_block, else_block)
            } else {
                ExtendedStmt::Stmt(stmt)
            }
        }

        pub(super) fn from_block(block: &Block) -> Vec<Self> {
            block
                .stmts
                .iter()
                .cloned()
                .map(ExtendedStmt::from)
                .collect()
        }
    }

    pub(super) struct DeclaredVarCollector {
        pub(super) variables: HashSet<String>,
    }

    impl DeclaredVarCollector {
        pub(super) fn new() -> Self {
            DeclaredVarCollector {
                variables: HashSet::new(),
            }
        }
    }

    impl<'ast> Visit<'ast> for DeclaredVarCollector {
        fn visit_local(&mut self, local: &'ast Local) {
            let var_name = syn_utils::get_declared_var_name(local);
            let already_contained = !self.variables.insert(var_name);
            assert!(
                !already_contained,
                "Variable {} redeclared",
                syn_utils::get_declared_var_name(local)
            );

            syn::visit::visit_local(self, local);
        }

        fn visit_stmt_macro(&mut self, stmt_macro: &'ast StmtMacro) {
            let macro_name = syn_utils::get_macro_name(stmt_macro);
            if macro_name == "assert" {
                let condition = syn_utils::get_assert_condition(stmt_macro);
                self.visit_expr(&condition);
            } else {
                panic!("Unsupported macro in drop elaboration: {macro_name}");
            }

            syn::visit::visit_stmt_macro(self, stmt_macro);
        }

        fn visit_expr_if(&mut self, _i: &'ast ExprIf) {
            // variables declared in smaller scopes should not be considered
        }
    }

    impl DeclaredVarCollector {
        pub(super) fn visit_extended_stmt_block(&mut self, stmts: &Vec<ExtendedStmt>) {
            for stmt in stmts {
                self.visit_extended_stmt(stmt);
            }
        }

        fn visit_extended_stmt(&mut self, stmt: &ExtendedStmt) {
            match stmt {
                ExtendedStmt::Stmt(stmt) => self.visit_stmt(stmt),
                ExtendedStmt::Drop(var) | ExtendedStmt::LastUseBeforeOverwrite(var) => {
                    panic!("Drop/LastUseBeforeOverwrite statement in drop elaboration: {var}")
                }
                ExtendedStmt::If(_, _, _) => {
                    // variables declared in smaller scopes should not be considered
                }
            }
        }
    }

    pub(super) struct VarCollector {
        pub(super) variables: HashSet<String>,
    }

    impl VarCollector {
        pub(super) fn new() -> Self {
            Self {
                variables: HashSet::new(),
            }
        }
    }

    impl<'ast> Visit<'ast> for VarCollector {
        fn visit_ident(&mut self, ident: &'ast Ident) {
            self.variables.insert(ident.to_string());
            syn::visit::visit_ident(self, ident);
        }

        fn visit_stmt_macro(&mut self, stmt_macro: &'ast StmtMacro) {
            let macro_name = syn_utils::get_macro_name(stmt_macro);
            if macro_name == "assert" {
                let condition = syn_utils::get_assert_condition(stmt_macro);
                self.visit_expr(&condition);
            } else {
                panic!("Unsupported macro in drop elaboration: {macro_name}");
            }

            syn::visit::visit_stmt_macro(self, stmt_macro);
        }
    }

    impl VarCollector {
        fn visit_extended_stmt_block(&mut self, stmts: &Vec<ExtendedStmt>) {
            for stmt in stmts {
                self.visit_extended_stmt(stmt);
            }
        }

        pub(super) fn visit_extended_stmt(&mut self, stmt: &ExtendedStmt) {
            match stmt {
                ExtendedStmt::Stmt(stmt) => self.visit_stmt(stmt),
                ExtendedStmt::Drop(var) | ExtendedStmt::LastUseBeforeOverwrite(var) => {
                    panic!("Drop/LastUseBeforeOverwrite statement in drop elaboration: {var}")
                }
                ExtendedStmt::If(condition, then_block, else_block) => {
                    self.visit_expr(condition);
                    self.visit_extended_stmt_block(then_block);
                    self.visit_extended_stmt_block(else_block);
                }
            }
        }
    }
}
