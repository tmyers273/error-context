/// Allows for converting from a child error type to a parent
/// error type while preserving any context on the child error.
///
/// This is intended to be used when:
///   1. Both Source and Target are context enriched thiserror enums
///   2. Source is a variant of Target's inner error
///
/// ** Example **
/// ```
/// use thiserror::Error;
///
/// use error_context::{Context, impl_context, impl_from_carry_context};
///
/// // Some inner error type
/// #[derive(Debug, Error)]
/// pub enum InnerError {
///     #[error("dummy")]
///     Dummy,
/// }
/// impl_context!(Inner(InnerError));
///
/// // And some outer error type, which contains
/// // a variant of the inner error type
/// #[derive(Debug, Error)]
/// pub enum OuterError {
///     #[error("inner error")]
///     // we explicitly do _not_ use #[from] here, instead
///     // opting to use the macro to create the conversion
///     // and handle the context propagation.
///     Inner(Inner),
/// }
/// impl_context!(Outer(OuterError));
///
/// // Then we use the macro to implement the conversion
/// // from Inner to Outer
/// impl_from_carry_context!(Inner, Outer, OuterError::Inner);
///
/// fn inner_call() -> Result<(), Inner> {
///     Err(InnerError::Dummy)
///         .context("context on inner")
/// }
///
/// fn outer_call() -> Result<(), Outer> {
///     inner_call().context("context on outer")
/// }
///
/// let r = outer_call();
/// assert!(r.is_err());
/// let e = r.unwrap_err();
/// assert_eq!(format!("{:?}",e), r#"Inner(Dummy)
///
/// Caused by:
///     0: context on outer
///     1: context on inner
/// "#);
/// ```
#[macro_export]
macro_rules! impl_from_carry_context {
    ($source: ident, $target: ident, $variant: path) => {
        impl From<$source> for $target {
            fn from(mut value: $source) -> Self {
                let mut contexts = vec![];

                let inner = loop {
                    match value {
                        $source::Base(x) => break x,
                        $source::Context { context, error } => {
                            contexts.push(context);
                            value = *error;
                        }
                    }
                };
                let inner = $source::Base(inner);

                let mut x = $target::Base($variant(inner));

                for ctx in contexts.into_iter().rev() {
                    x = $target::Context {
                        context: ctx,
                        error: Box::new(x),
                    };
                }

                x
            }
        }
    };
}

pub use impl_from_carry_context;
