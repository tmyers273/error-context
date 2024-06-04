//! This library provides a wrapper around an existing (and usually strongly typed)
//! error type, from which you can add additional context.
//!
//! This is meant to provide the best of both worlds between [thiserror] and [anyhow]
//! in that you retain the type of the underlying root error, while allowing you to
//! add additional context to it.
//!
//! It is intended to be used with [thiserror] enums, but should work with any error type.
//!
//! ** Example **
//! ```
//! use thiserror::Error;
//! use thiserror_context::{Context, impl_context};
//!
//! #[derive(Debug, Error)]
//! pub enum MyErrorInner {
//!     #[error("parse int err: {0}")]
//!     ParseInt(#[from] std::num::ParseIntError),
//! }
//!
//! // Defines a new type, `MyError`, that wraps `MyErrorInner` and allows
//! // additional context to be added.
//! impl_context!(MyError(MyErrorInner));
//!
//! fn t(value: &str) -> Result<i64, MyError> {
//!     let v: i64 = value
//!         .parse()
//!         .with_context(|| format!("failed to parse {}", value))?;
//!     Ok(v)
//! }
//!
//!
//! ```
//!
//! [thiserror]: https://docs.rs/thiserror
//! [anyhow]: https://docs.rs/anyhow
use std::fmt::{Debug, Display};

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
                f.write_fmt(format_args!("{}\n\nCaused by:\n", root))?;

                for (i, context) in context.iter().enumerate() {
                    f.write_fmt(format_args!("    {i}: {}\n", context))?;
                }
                Ok(())
            }
        }

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

        impl<T, E: Into<$out>> Context<T, E, $out> for Result<T, E> {
            fn context<C>(self, context: C) -> Result<T, $out>
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

            fn with_context<C, F>(self, f: F) -> Result<T, $out>
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

pub trait Context<T, E, W>
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
        let r: Result<(), DummyErrorInner> = Err(DummyErrorInner::Dummy);

        let r = r
            .context("first")
            .with_context(|| format!("second dynamic"))
            .context("third");

        let r = format!("{:#?}", r.unwrap_err());

        assert_eq!(
            r,
            "dummy err msg\n\nCaused by:\n    0: third\n    1: second dynamic\n    2: first\n"
        );
    }

    #[test]
    fn it_works2() {
        let r = t().context("parsing test").context("second");

        let r = format!("{:#?}", r.unwrap_err());

        assert_eq!(
            r,
            "parse int err: invalid digit found in string\n\nCaused by:\n    0: second\n    1: parsing test\n",
        );
    }
}
