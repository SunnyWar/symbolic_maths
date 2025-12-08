// src/conv/types.rs
use indexmap::IndexSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatTy {
    F32,
    F64,
    Unknown,
}

pub struct ConversionContext {
    pub params: IndexSet<String>,
    pub float_ty: FloatTy,
}

impl ConversionContext {
    pub fn is_f64(&self) -> bool {
        self.float_ty == FloatTy::F64
    }
}

// optional short alias
pub type ConvCtx = ConversionContext;

pub fn detect_primary_float(sig: &syn::Signature) -> FloatTy {
    use syn::{ReturnType, Type};
    // check return type first
    if let ReturnType::Type(_, ty) = &sig.output {
        if let Type::Path(tp) = &**ty {
            if let Some(seg) = tp.path.segments.last() {
                match seg.ident.to_string().as_str() {
                    "f32" => return FloatTy::F32,
                    "f64" => return FloatTy::F64,
                    _ => {}
                }
            }
        }
    }
    // then check params
    for input in &sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            if let Type::Path(tp) = &*pat_type.ty {
                if let Some(seg) = tp.path.segments.last() {
                    match seg.ident.to_string().as_str() {
                        "f32" => return FloatTy::F32,
                        "f64" => return FloatTy::F64,
                        _ => {}
                    }
                }
            }
        }
    }
    FloatTy::Unknown
}
