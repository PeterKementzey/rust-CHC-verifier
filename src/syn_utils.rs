use syn::Local;

pub(crate) fn get_local_var_name(local: &Local) -> String {
    match &local.pat {
        syn::Pat::Ident(syn::PatIdent { ident, .. }) => ident.to_string(),
        _ => panic!("Local variable declaration pattern is not an identifier"),
    }
}

pub(crate) fn get_var_name(path: &syn::ExprPath) -> String {
    path.path.get_ident().expect("Could not get variable name").to_string()
}
