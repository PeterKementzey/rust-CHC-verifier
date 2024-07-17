use std::collections::HashSet;

use itertools::Itertools;
use syn::{visit::Visit, Block, ExprIf, Local, StmtMacro};
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

    fn visit_expr_if(&mut self, _i: &'ast ExprIf) {
        // variables declared in smaller scopes should not be considered
    }
}

impl DeclaredVarCollector {
    fn visit_extended_stmt_block(&mut self, stmts: &Vec<ExtendedStmt>) {
        for stmt in stmts {
            self.visit_extended_stmt(stmt);
        }
    }

    fn visit_extended_stmt(&mut self, stmt: &ExtendedStmt) {
        match stmt {
            ExtendedStmt::Stmt(stmt) => self.visit_stmt(stmt),
            ExtendedStmt::Drop(var) => {
                panic!("Drop statement in drop elaboration: {var}")
            }
            ExtendedStmt::If(_, _, _) => {
                // variables declared in smaller scopes should not be considered
            }
        }
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

impl VarCollector {
    fn visit_extended_stmt(&mut self, stmt: &ExtendedStmt) {
        match stmt {
            ExtendedStmt::Stmt(stmt) => self.visit_stmt(stmt),
            ExtendedStmt::Drop(var) => {
                panic!("Drop statement in drop elaboration: {var}")
            }
            ExtendedStmt::If(condition, then_block, else_block) => {
                self.visit_expr(condition);
                for stmt in then_block {
                    self.visit_extended_stmt(stmt);
                }
                if let Some(else_block) = else_block {
                    for stmt in else_block {
                        self.visit_extended_stmt(stmt);
                    }
                }
            }
        }
    }
}

fn add_drops_to_block(stmts: &mut Vec<ExtendedStmt>, variables_to_drop: &mut HashSet<String>) {
    for i in (0..stmts.len()).rev() {
        match &mut stmts[i] {
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
                    stmts.insert(i + 1, ExtendedStmt::Drop(var.clone()));
                    variables_to_drop.remove(var);
                }
            }
            if_stmt @ ExtendedStmt::If(_, _, _) => {
                let mut last_used_vars: HashSet<String> = {
                    let mut collector = VarCollector::new();
                    collector.visit_extended_stmt(if_stmt);
                    collector
                        .variables
                        .iter()
                        .filter(|var| variables_to_drop.contains(*var))
                        .cloned()
                        .collect()
                };

                variables_to_drop.retain(|var| !last_used_vars.contains(var));

                #[allow(clippy::items_after_statements)]
                fn add_drops_to_if_branch(
                    branch_stmts: &mut Vec<ExtendedStmt>,
                    last_used_vars: &mut HashSet<String>,
                ) {
                    let locally_declared_vars: HashSet<String> = {
                        let mut collector = DeclaredVarCollector::new();
                        collector.visit_extended_stmt_block(branch_stmts);
                        collector.variables
                    };
                    last_used_vars.extend(locally_declared_vars.iter().cloned());
                    add_drops_to_block(branch_stmts, last_used_vars);
                    let remaining_vars: Vec<String> =
                        last_used_vars.iter().sorted().cloned().collect();
                    for var in remaining_vars.iter().rev() {
                        branch_stmts.insert(0, ExtendedStmt::Drop(var.clone()));
                    }
                }

                if let ExtendedStmt::If(_, then_block, else_block) = if_stmt {
                    add_drops_to_if_branch(then_block, &mut last_used_vars.clone());
                    if let Some(else_block) = else_block {
                        add_drops_to_if_branch(else_block, &mut last_used_vars);
                    }
                } else {
                    unreachable!()
                }
            }
            ExtendedStmt::Drop(_) => panic!("Drop statement in drop elaboration"),
        }
    }
}

pub(crate) fn perform_drop_elaboration(block: &Block) -> Vec<ExtendedStmt> {
    let mut variables_to_drop: HashSet<String> = {
        let mut collector = DeclaredVarCollector::new();
        collector.visit_block(block);
        collector.variables
    };

    let mut extended_stmts: Vec<ExtendedStmt> = ExtendedStmt::from_block(block);

    add_drops_to_block(&mut extended_stmts, &mut variables_to_drop);

    assert!(
        variables_to_drop.is_empty(),
        "Variables not dropped: {variables_to_drop:?}"
    );

    extended_stmts
}
