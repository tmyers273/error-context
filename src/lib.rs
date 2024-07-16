//! This library provides a wrapper around a [thiserror] enum, from which
//! you can add additional context, similar to how you would with the [anyhow]
//! crate.
//!
//! This crate is meant to bridge the gap and provide the best of both worlds between
//! [thiserror] and [anyhow], in that you retain the type of the underlying root error,
//! while allowing you to add additional context to it.
//!
//! # Problem
//!
//! ## With [thiserror]
//!
//! Using [thiserror], you can end up with errors similar to
//! ```text
//! Sqlx(RowNotFound)
//! ```
//! which is not helpful in debugging.
//!
//! ## With [anyhow]
//!
//! Using [anyhow] gives you much more helpful context:
//!
//! ```text ignore
//! Sqlx(RowNotFound)
//!
//! Caused by:
//!   0: loading user id 1
//!   1: authentication
//! ```
//!
//! But it comes at the expense of erasing the underlying error type.
//!
//! This type erasure is problematic in a few ways:
//! - if you want to preserve the ability to use your [thiserror] type, it
//!   forces you to convert all your errors in your [thiserror] type. This
//!   is particularly easy to forget to do, as [anyhow] will happily accept
//!   any error.
//! - if you forget to convert an error into your [thiserror] type and you want
//!   to have something approximating the match on your [thiserror] type, then
//!   you need to attempt to downcast all the possible variants of the [thiserror]
//!   type. In turn, that means you need to add a downcast attempt for any new
//!   variants you add to your [thiserror] type. This introduces an easy thing
//!   to forget to do.
//!
//! In a happy case, _if_ you remember to convert _all_ your errors into your [thiserror]
//! type, then you can downcast directly to the [thiserror] type.
//!
//! ```
//! use anyhow::Context;
//! use thiserror::Error;
//!
//! #[derive(Debug, Error)]
//! enum ThisError {
//!     #[error("placeholder err")]
//!     Placeholder,
//!
//!     #[error("sqlx err: {0}")]
//!     Sqlx(#[from] sqlx::Error),
//! }
//!
//! async fn my_fn() -> anyhow::Result<()> {
//!     async {
//!         // Some db query or something
//!        Err(sqlx::Error::RowNotFound)
//!     }.await
//!         .map_err(ThisError::from) // <-------------- Important!
//!         .context("my_fn")?;
//!     Ok(())
//! }
//!
//! async fn caller() -> anyhow::Result<()> {
//!     let r: anyhow::Result<()> = my_fn().await;
//!
//!     if let Err(e) = r {
//!         // So even though we can't match on an anyhow error
//!         // match r {
//!         //     Placeholder => { },
//!         //     Sqlx(_) => { },
//!         // }
//!
//!         // We can downcast it to a ThisError, then match on that
//!         if let Some(x) = e.downcast_ref::<ThisError>() {
//!             match x {
//!                 ThisError::Placeholder => {},
//!                 ThisError::Sqlx(_) => {},
//!             }
//!         }
//!     }
//!
//!     Ok(())
//! }
//! ```
//!
//! But, if you forget to convert your error into your [thiserror] type,
//! then things start to get messy.
//!
//! ```
//! use anyhow::Context;
//! use thiserror::Error;
//!
//! #[derive(Debug, Error)]
//! enum ThisError {
//!     #[error("placeholder err")]
//!     Placeholder,
//!
//!     #[error("sqlx err: {0}")]
//!     Sqlx(#[from] sqlx::Error),
//! }
//!
//! async fn my_fn() -> anyhow::Result<()> {
//!     async {
//!         // Some db query or something
//!        Err(sqlx::Error::RowNotFound)
//!     }.await
//!         .context("my_fn")?; // <----------- No intermediary conversion into ThisError
//!     Ok(())
//! }
//!
//! async fn caller() -> anyhow::Result<()> {
//!     let r: anyhow::Result<()> = my_fn().await;
//!
//!     if let Err(e) = r {
//!         // We still can't match on an anyhow error
//!         // match r {
//!         //     Placeholder => { },
//!         //     Sqlx(_) => { },
//!         // }
//!
//!         if let Some(x) = e.downcast_ref::<ThisError>() {
//!             // We forgot to explicitly convert our error,
//!             // so this will never run
//!             unreachable!("This will never run");
//!         }
//!
//!         // So, to be safe, we can start attempting to downcast
//!         // all the error types that `ThisError` supports?
//!         if let Some(x) = e.downcast_ref::<sqlx::Error>() {
//!             // That's okay if ThisError is relatively small,
//!             // but it's error prone in that we have to remember
//!             // to add another downcast attempt for any new
//!             // error variants that are added to `ThisError`
//!         }
//!     }
//!
//!     Ok(())
//! }
//! ```
//!
//! # Solution
//!
//! This crate bridges the two worlds, allowing you to add context to your [thiserror] type
//! while preserving the ergonomics and accessibility of the underlying error enum.
//!
//! This crate is intended to be used with [thiserror] enums, but should work with any error type.
//!
//! ** Example **
//! ```
//! use thiserror::Error;
//! use error_context::{Context, impl_context};
//!
//! // A normal, run-of-the-mill thiserror enum
//! #[derive(Debug, Error)]
//! enum ThisErrorInner {
//!     #[error("placeholder err")]
//!     Placeholder,
//!
//!     #[error("sqlx err: {0}")]
//!     Sqlx(#[from] sqlx::Error),
//! }
//!
//! // Defines a new type, `ThisErr`, that wraps `ThisErrorInner` and allows
//! // additional context to be added.
//! impl_context!(ThisError(ThisErrorInner));
//!
//! // We are returning the wrapped new type, `ThisError`, instead of the
//! // underlying `ThisErrorInner`.
//! async fn my_fn() -> Result<(), ThisError> {
//!     async {
//!         // Some db query or something
//!        Err(sqlx::Error::RowNotFound)
//!     }.await
//!         .context("my_fn")?;
//!     Ok(())
//! }
//!
//! async fn caller() -> anyhow::Result<()> {
//!     let r: Result<(), ThisError> = my_fn().await;
//!
//!     if let Err(e) = r {
//!         // We can now match on the error type!
//!         match e.as_ref() {
//!             ThisErrorInner::Placeholder => {},
//!             ThisErrorInner::Sqlx(_) => {},
//!         }
//!     }
//!
//!     Ok(())
//! }
//! ```
//!
//! # Usage
//!
//! Similar to [context], this crate provides a [Context] trait that extends
//! the [Result] type with two methods: `context` and `with_context`.
//!
//! [context](Context::context) adds static context to the error, while
//! [with_context](Context::with_context) adds dynamic context to the error.
//!
//! ```
//! use thiserror::Error;
//! use error_context::{Context, impl_context};
//!
//! #[derive(Debug, Error)]
//! enum ThisErrorInner {
//!     #[error("placeholder err")]
//!     Placeholder,
//! }
//! impl_context!(ThisError(ThisErrorInner));
//!
//! fn f(id: i64) -> Result<(), ThisError> {
//!     Err(ThisErrorInner::Placeholder.into())
//! }
//!
//! fn t(id: i64) -> Result<(), ThisError> {
//!     f(id)
//!         .context("some static context")
//!         .with_context(|| format!("for id {}", id))
//! }
//!
//! let res = t(1);
//! assert!(res.is_err());
//! let err = res.unwrap_err();
//! let debug_repr = format!("{:#?}", err);
//! assert_eq!(r#"Placeholder
//!
//! Caused by:
//!     0: for id 1
//!     1: some static context
//! "#, debug_repr);
//! ```
//!
//! # Nesting
//!
//! Context enriched errors can be nested and they will preserve their
//! context messages when converting from a child error type to a parent.
//!
//! See [impl_from_carry_context] for more information.
pub mod composition;

use std::fmt::Display;

/// Defines a new struct that wraps the error type, allowing additional
/// context to be added.
///
/// The wrapped error type is intended to be a [thiserror](https://docs.rs/thiserror) enum, but
/// should work with any error type.
///
/// The wrapper will implement all the [From] methods that the wrapped
/// error type implements.
///
/// Ultimately, this allows [anyhow](https://docs.rs/anyhow)-like `context` and `with_context`
/// calls on a strongly typed error.
///
/// ** Example **
/// ```ignore
/// impl_context!(DummyError(DummyErrorInner));
/// ```
#[macro_export]
macro_rules! impl_context {
    ($out:ident($ty:ty)) => {
        impl<T: Into<$ty>> From<T> for $out {
            fn from(value: T) -> Self {
                $out::Base(value.into())
            }
        }

        pub enum $out {
            Base($ty),
            Context { error: Box<$out>, context: String },
        }

        impl $out {
            pub fn into_inner(self) -> $ty {
                match self {
                    $out::Base(b) => b,
                    $out::Context { error, .. } => error.into_inner(),
                }
            }

            /// Returns all the context messages and the root error.
            fn all<'a>(&'a self, mut context: Vec<&'a String>) -> (Vec<&String>, &$ty) {
                match self {
                    $out::Base(b) => (context, b),
                    $out::Context { error, context: c } => {
                        context.push(c);
                        error.all(context)
                    }
                }
            }
        }

        impl std::fmt::Debug for $out {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let (context, root) = self.all(vec![]);
                f.write_fmt(format_args!("{:?}", root))?; //Caused by:\n", root))?;

                if !context.is_empty() {
                    f.write_fmt(format_args!("\n\nCaused by:\n"))?;
                }

                for (i, context) in context.iter().enumerate() {
                    f.write_fmt(format_args!("    {i}: {}\n", context))?;
                }
                Ok(())
            }
        }

        impl std::fmt::Display for $out {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_fmt(format_args!("{}", self.as_ref()))
            }
        }

        impl std::error::Error for $out {}

        impl AsRef<$ty> for $out {
            fn as_ref(&self) -> &$ty {
                match self {
                    $out::Base(b) => b,
                    // One to get out of the Box, and another to
                    // recursively call this method.
                    $out::Context { error, .. } => error.as_ref().as_ref(),
                }
            }
        }

        impl<Z, E: Into<$out>> Context<$out, Z, E> for Result<Z, E> {
            fn context<C>(self, context: C) -> Result<Z, $out>
            where
                C: std::fmt::Display + Send + Sync + 'static,
            {
                match self {
                    Ok(t) => Ok(t),
                    Err(e) => {
                        let out: $out = e.into();
                        Err($out::Context {
                            error: Box::new(out),
                            context: context.to_string(),
                        })
                    }
                }
            }

            fn with_context<C, F>(self, f: F) -> Result<Z, $out>
            where
                C: std::fmt::Display + Send + Sync + 'static,
                F: FnOnce() -> C,
            {
                match self {
                    Ok(t) => Ok(t),
                    Err(e) => {
                        let out: $out = e.into();
                        Err($out::Context {
                            error: Box::new(out),
                            context: format!("{}", f()),
                        })
                    }
                }
            }
        }
    };
}

pub trait Context<W, T, E>
where
    E: Into<W>,
{
    /// Wrap the error value with additional context.
    fn context<C>(self, context: C) -> Result<T, W>
    where
        C: Display + Send + Sync + 'static;

    /// Wrap the error value with additional context that is evaluated lazily
    /// only once an error does occur.
    fn with_context<C, F>(self, f: F) -> Result<T, W>
    where
        C: Display + Send + Sync + 'static,
        F: FnOnce() -> C;
}

#[cfg(test)]
mod tests {
    use super::*;
    use thiserror::Error;

    #[derive(Debug, Error)]
    pub enum DummyErrorInner {
        #[error("dummy err msg")]
        Dummy,
        #[error("parse int err: {0}")]
        ParseInt(#[from] std::num::ParseIntError),
    }

    impl_context!(DummyError(DummyErrorInner));

    fn t() -> Result<(), DummyError> {
        let _: i64 = "fake".parse()?;
        Ok(())
    }

    #[test]
    fn it_works() {
        let r = t()
            .context("first")
            .with_context::<String, _>(|| format!("second dynamic"))
            .context("third"); //: Result<(), DummyError> = Err(DummyErrorInner::Dummy.into());

        let res = format!("{:#?}", r.as_ref().unwrap_err());

        assert_eq!(
            res,
            "ParseInt(ParseIntError { kind: InvalidDigit })\n\nCaused by:\n    0: third\n    1: second dynamic\n    2: first\n"
        );
    }

    #[test]
    fn it_works2() {
        let r = t().context("parsing test").context("second");

        let r = format!("{:#?}", r.unwrap_err());

        assert_eq!(
            r,
            "ParseInt(ParseIntError { kind: InvalidDigit })\n\nCaused by:\n    0: second\n    1: parsing test\n",
        );
    }

    #[test]
    fn no_contrext_omits_causation() {
        let r = t();

        let r = format!("{:#?}", r.unwrap_err());

        assert_eq!(r, "ParseInt(ParseIntError { kind: InvalidDigit })",);
    }
}

#[cfg(test)]
mod composable_tests {
    use super::*;
    use inner::DummyError;
    use thiserror::Error;

    mod inner {
        use crate::Context;
        use thiserror::Error;

        #[derive(Debug, Error)]
        pub enum DummyErrorInner {
            #[error("dummy err msg")]
            Dummy,
            #[error("parse int err: {0}")]
            ParseInt(#[from] std::num::ParseIntError),
        }
        impl_context!(DummyError(DummyErrorInner));

        pub fn t() -> Result<(), DummyError> {
            Err::<(), DummyErrorInner>(DummyErrorInner::Dummy.into())
                .context("first")
                .context("second")
        }
    }

    #[derive(Debug, Error)]
    pub enum OtherInner {
        #[error("t {0}")]
        T(DummyError),
    }

    impl_from_carry_context!(DummyError, Other, OtherInner::T);

    impl_context!(Other(OtherInner));

    fn wrapped() -> Result<(), Other> {
        _wrapped().context("fourth")
    }

    fn _wrapped() -> Result<(), Other> {
        inner::t().context("third")
    }

    #[test]
    fn it_is_composable() {
        let r = wrapped();

        let r = format!("{:#?}", r.unwrap_err());

        assert_eq!(
            r,
            "T(Dummy)\n\nCaused by:\n    0: fourth\n    1: third\n    2: second\n    3: first\n",
        );
    }
}
