use std::collections::HashSet;

use itertools::Itertools;
use syn::{visit::Visit, Block, Local, StmtMacro};
use syn::{Ident, Stmt};

use crate::syn_utils;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ExtendedStmt {
    Stmt(Stmt),
    Drop(String),
    If(syn::Expr, Vec<ExtendedStmt>, Option<Vec<ExtendedStmt>>),
}

impl ExtendedStmt {
    fn from(stmt: Stmt) -> Self {
        if let Stmt::Expr(syn::Expr::If(if_expr), _) = &stmt {
            let condition = if_expr.cond.as_ref().clone();
            let then_block = ExtendedStmt::from_block(&if_expr.then_branch);
            let else_block = syn_utils::get_else_block(if_expr).map(ExtendedStmt::from_block);

            ExtendedStmt::If(condition, then_block, else_block)
        } else {
            ExtendedStmt::Stmt(stmt)
        }
    }

    fn from_block(block: &Block) -> Vec<Self> {
        block
            .stmts
            .iter()
            .cloned()
            .map(ExtendedStmt::from)
            .collect()
    }
}

struct DeclaredVarCollector {
    variables: HashSet<String>,
}

impl DeclaredVarCollector {
    fn new() -> Self {
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
}

struct VarCollector {
    variables: HashSet<String>,
}

impl VarCollector {
    fn new() -> Self {
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

pub(crate) fn perform_drop_elaboration(block: &Block) -> Vec<ExtendedStmt> {
    let mut variables_to_drop: HashSet<String> = {
        let mut collector = DeclaredVarCollector::new();
        collector.visit_block(block);
        collector.variables
    };

    let mut extended_stmts: Vec<ExtendedStmt> = ExtendedStmt::from_block(block);

    for i in (0..extended_stmts.len()).rev() {
        match &extended_stmts[i] {
            ExtendedStmt::Stmt(stmt) => {
                let last_used_vars: Vec<String> = {
                    let mut collector = VarCollector::new();
                    collector.visit_stmt(stmt);
                    collector
                        .variables
                        .iter()
                        .filter(|var| variables_to_drop.contains(*var))
                        .sorted()
                        .cloned()
                        .collect()
                };

                for var in last_used_vars.iter().rev() {
                    extended_stmts.insert(i + 1, ExtendedStmt::Drop(var.clone()));
                    variables_to_drop.remove(var);
                }
            }
            ExtendedStmt::If(condition, then_block, else_block) => {
                // TODO
            }
            ExtendedStmt::Drop(_) => panic!("Drop statement in drop elaboration"),
        }
    }

    assert!(
        variables_to_drop.is_empty(),
        "Variables not dropped: {variables_to_drop:?}"
    );

    extended_stmts
}
