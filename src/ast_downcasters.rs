use core::panic;

use syn::{Expr, Item, Stmt};

pub(crate) fn downcast_item(item: Item) -> &'static str {
    match item {
        Item::Fn(_) => {
            return "Function";
        }
        Item::Const(_) => {
            return "Const";
        }
        Item::Enum(_) => {
            return "Enum";
        }
        Item::ExternCrate(_) => {
            return "ExternCrate";
        }
        Item::ForeignMod(_) => {
            return "ForeignMod";
        }
        Item::Impl(_) => {
            return "Impl";
        }
        Item::Macro(_) => {
            return "Macro";
        }
        Item::Mod(_) => {
            return "Mod";
        }
        Item::Static(_) => {
            return "Static";
        }
        Item::Struct(_) => {
            return "Struct";
        }
        Item::Trait(_) => {
            return "Trait";
        }
        Item::TraitAlias(_) => {
            return "TraitAlias";
        }
        Item::Type(_) => {
            return "Type";
        }
        Item::Union(_) => {
            return "Union";
        }
        Item::Use(_) => {
            return "Use";
        }
        Item::Verbatim(_) => {
            return "Verbatim";
        }
        _ => {
            panic!("Could not downcast item type")
        }
    }
}

pub(crate) fn downcast_statement(stmt: Stmt) -> &'static str {
    match stmt {
        Stmt::Local(_) => {
            return "Local";
        }
        Stmt::Item(_) => {
            return "Item";
        }
        Stmt::Expr(..) => {
            return "Expr";
        }
        Stmt::Macro(_) => {
            return "Macro";
        }
    }
}

pub(crate) fn downcast_expression(expr: Expr) -> &'static str {
    match expr {
        Expr::Array(_) => {
            return "Array";
        }
        Expr::Assign(_) => {
            return "Assign";
        }
        Expr::Async(_) => {
            return "Async";
        }
        Expr::Await(_) => {
            return "Await";
        }
        Expr::Binary(_) => {
            return "Binary";
        }
        Expr::Block(_) => {
            return "Block";
        }
        Expr::Break(_) => {
            return "Break";
        }
        Expr::Call(_) => {
            return "Call";
        }
        Expr::Cast(_) => {
            return "Cast";
        }
        Expr::Closure(_) => {
            return "Closure";
        }
        Expr::Const(_) => {
            return "Const";
        }
        Expr::Continue(_) => {
            return "Continue";
        }
        Expr::Field(_) => {
            return "Field";
        }
        Expr::ForLoop(_) => {
            return "ForLoop";
        }
        Expr::Group(_) => {
            return "Group";
        }
        Expr::If(_) => {
            return "If";
        }
        Expr::Index(_) => {
            return "Index";
        }
        Expr::Infer(_) => {
            return "Infer";
        }
        Expr::Let(_) => {
            return "Let";
        }
        Expr::Lit(_) => {
            return "Lit";
        }
        Expr::Loop(_) => {
            return "Loop";
        }
        Expr::Macro(_) => {
            return "Macro";
        }
        Expr::Match(_) => {
            return "Match";
        }
        Expr::MethodCall(_) => {
            return "MethodCall";
        }
        Expr::Paren(_) => {
            return "Paren";
        }
        Expr::Path(_) => {
            return "Path";
        }
        Expr::Range(_) => {
            return "Range";
        }
        Expr::Reference(_) => {
            return "Reference";
        }
        Expr::Repeat(_) => {
            return "Repeat";
        }
        Expr::Return(_) => {
            return "Return";
        }
        Expr::Struct(_) => {
            return "Struct";
        }
        Expr::Try(_) => {
            return "Try";
        }
        Expr::TryBlock(_) => {
            return "TryBlock";
        }
        Expr::Tuple(_) => {
            return "Tuple";
        }
        Expr::Unary(_) => {
            return "Unary";
        }
        Expr::Unsafe(_) => {
            return "Unsafe";
        }
        Expr::Verbatim(_) => {
            return "Verbatim";
        }
        Expr::While(_) => {
            return "While";
        }
        Expr::Yield(_) => {
            return "Yield";
        }
        _ => {
            panic!("Could not downcast expression type")
        }
    }
}
