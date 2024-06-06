use syn::Local;

pub(crate) fn get_declared_var_name(local: &Local) -> String {
    fn get_name(pat: &syn::Pat) -> String {
        match pat {
            syn::Pat::Ident(syn::PatIdent { ident, .. }) => ident.to_string(),
            syn::Pat::Type(syn::PatType { pat, .. }) => get_name(pat),
            _ => panic!(
                "Local variable declaration pattern is not an identifier {:?}",
                pat
            ),
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

pub(super) fn get_referenced_name(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Reference(reference) => match &*reference.expr {
            syn::Expr::Path(path) => get_var_name(path),
            _ => panic!("Expected path expression in reference {:?}", reference),
        },
        _ => panic!("Expected reference expression {:?}", expr),
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
    let macro_name = get_macro_name(&stmt_macro);
    if macro_name != "assert" {
        panic!(
            "get_assert_condition called with wrong macro: {}",
            macro_name
        );
    }
    let condition: syn::Expr = syn::parse2(stmt_macro.mac.tokens.clone())
        .expect("Failed to parse macro tokens as expression");
    condition
}

pub(crate) fn is_borrow(local: &Local) -> bool {
    match &local.init {
        Some(local_init) => matches!(*local_init.expr, syn::Expr::Reference(_)),
        None => false,
    }
}
