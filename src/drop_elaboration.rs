use std::collections::{HashMap, HashSet};

use syn::{visit::Visit, Block, Local};
use syn::{Expr, Stmt};

use crate::syn_utils::{get_local_var_name, get_var_name};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ExtendedStmt {
    Stmt(Stmt),
    Drop(String),
}

struct VarUsageCollector {
    usages: HashMap<String, usize>,
    current_stmt_index: usize,
}

impl VarUsageCollector {
    fn new() -> Self {
        VarUsageCollector {
            usages: HashMap::new(),
            current_stmt_index: 0,
        }
    }
}

impl<'ast> Visit<'ast> for VarUsageCollector {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if let Expr::Path(path) = expr {
            let var_name = get_var_name(&path);
            if self
                .usages
                .insert(var_name, self.current_stmt_index)
                .is_none()
            {
                panic!(
                    "Variable {} encountered before declaration",
                    get_var_name(&path)
                );
            }
        }

        syn::visit::visit_expr(self, expr);
    }

    fn visit_local(&mut self, local: &'ast Local) {
        let var_name = get_local_var_name(&local);
        if self
            .usages
            .insert(var_name, self.current_stmt_index)
            .is_some()
        {
            panic!("Variable {} redeclared", get_local_var_name(&local));
        }

        syn::visit::visit_local(self, local);
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        syn::visit::visit_stmt(self, stmt);
        self.current_stmt_index += 1;
    }
}

pub(crate) fn perform_drop_elaboration(block: &Block) -> Vec<ExtendedStmt> {
    let last_usages: HashMap<usize, HashSet<String>> = {
        let mut collector = VarUsageCollector::new();
        collector.visit_block(block);

        let mut last_usages = HashMap::new();
        for (var, stmt_index) in collector.usages {
            last_usages
                .entry(stmt_index)
                .or_insert_with(HashSet::new)
                .insert(var);
        }

        last_usages
    };

    let mut extended_stmts = Vec::new();
    let mut stmt_index = 0;

    for stmt in &block.stmts {
        extended_stmts.push(ExtendedStmt::Stmt(stmt.clone()));

        for var in last_usages.get(&stmt_index).unwrap_or(&HashSet::new()) {
            extended_stmts.push(ExtendedStmt::Drop(var.clone()));
        }

        stmt_index += 1;
    }

    extended_stmts
}
