// src/literals.rs
use anyhow::Result;
use quote::ToTokens;
use syn::Lit;

use crate::types::{ConversionContext, FloatTy};

/// Convert a syn literal into the canonical s-expression literal string,
/// emitting float literals as plain decimal tokens (no f32/f64 suffix).
pub fn convert_literal(lit: &Lit, ctx: &ConversionContext) -> Result<String> {
    match lit {
        Lit::Float(lf) => {
            // parse to f64 for stable formatting
            let v: f64 = lf.base10_parse()?;
            let s = if ctx.float_ty == FloatTy::F64 {
                emit_float_literal_f64(v)
            } else if ctx.float_ty == FloatTy::F32 {
                emit_float_literal_f32(v as f32)
            } else {
                // Unknown target: preserve original token text but normalize spacing
                lf.to_token_stream().to_string()
            };
            Ok(s)
        }
        Lit::Int(li) => {
            // keep integer literals as-is
            Ok(li.base10_digits().to_string())
        }
        Lit::Bool(lb) => Ok(lb.value.to_string()),
        Lit::Char(lc) => Ok(format!("'{}'", lc.value())),
        Lit::Str(ls) => Ok(format!("\"{}\"", ls.value())),
        other => {
            // fallback: preserve token text
            Ok(other.to_token_stream().to_string())
        }
    }
}

/// Format an f64 for s-expression emission (no suffix).
/// Use 17 digits which is safe for round-trip representation of f64.
fn emit_float_literal_f64(v: f64) -> String {
    // Trim trailing zeros and possible trailing decimal point for nicer output.
    let s = format!("{:.17}", v);
    normalize_decimal_string(&s)
}

/// Format an f32 for s-expression emission (no suffix).
/// Use 9 digits which is safe for round-trip representation of f32.
fn emit_float_literal_f32(v: f32) -> String {
    let s = format!("{:.9}", v);
    normalize_decimal_string(&s)
}

/// Normalize a decimal string: remove trailing zeros after decimal point,
/// and remove the decimal point if the number is integral (e.g., "42.000" -> "42").
fn normalize_decimal_string(s: &str) -> String {
    if let Some(dot_pos) = s.find('.') {
        // split integer and fractional parts
        let (int_part, frac_part) = s.split_at(dot_pos);
        // frac_part starts with '.'
        let mut frac = &frac_part[1..];
        // remove trailing zeros
        while frac.ends_with('0') {
            frac = &frac[..frac.len() - 1];
        }
        if frac.is_empty() {
            int_part.to_string()
        } else {
            format!("{}.{}", int_part, frac)
        }
    } else {
        s.to_string()
    }
}
