use syn::{Expr, Local};

pub(crate) fn get_declared_var_name(local: &Local) -> String {
    fn get_name(pat: &syn::Pat) -> String {
        match pat {
            syn::Pat::Ident(syn::PatIdent { ident, .. }) => ident.to_string(),
            syn::Pat::Type(syn::PatType { pat, .. }) => get_name(pat),
            _ => panic!("Local variable declaration pattern is not an identifier {pat:?}"),
        }
    }

    get_name(&local.pat)
}

pub(crate) fn get_var_name(path: &syn::ExprPath) -> String {
    path.path
        .get_ident()
        .expect("Could not get variable name")
        .to_string()
}

pub(super) fn get_borrowed_name(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Reference(reference) => match &*reference.expr {
            syn::Expr::Path(path) => get_var_name(path),
            _ => panic!("Expected path expression in reference {reference:?}"),
        },
        _ => panic!("Expected reference expression {expr:?}"),
    }
}

pub(crate) fn get_macro_name(stmt_macro: &syn::StmtMacro) -> String {
    stmt_macro
        .mac
        .path
        .get_ident()
        .expect("Could not get macro name")
        .to_string()
}

pub(crate) fn get_assert_condition(stmt_macro: &syn::StmtMacro) -> syn::Expr {
    let macro_name = get_macro_name(stmt_macro);
    assert_eq!(
        macro_name, "assert",
        "get_assert_condition called with wrong macro: {macro_name}"
    );
    let condition: syn::Expr = syn::parse2(stmt_macro.mac.tokens.clone())
        .expect("Failed to parse macro tokens as expression");
    condition
}

pub(crate) fn is_borrow(expr: &syn::Expr) -> bool {
    matches!(expr, syn::Expr::Reference(_))
}

pub(crate) fn get_init_expr(local: &Local) -> Option<&syn::Expr> {
    local
        .init
        .as_ref()
        .map(|syn::LocalInit { expr, .. }| &**expr)
}

pub(crate) fn get_else_block(if_expr: &syn::ExprIf) -> Option<&syn::Block> {
    if_expr.else_branch.as_ref().map(|(_, block)| {
        if let Expr::Block(block) = block.as_ref() {
            &block.block
        } else {
            panic!("Else branch of if statement is not a block")
        }
    })
}
