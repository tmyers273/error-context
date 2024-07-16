This library provides a wrapper around a [thiserror] enum, from which
you can add additional context, similar to how you would with the [anyhow]
crate.

This crate is meant to bridge the gap and provide the best of both worlds between
[thiserror] and [anyhow], in that you retain the type of the underlying root error,
while allowing you to add additional context to it.

# Problem

## With [thiserror]

Using [thiserror], you can end up with errors similar to

```text
Sqlx(RowNotFound)
```

which is not helpful in debugging.

## With [anyhow]

Using [anyhow] gives you much more helpful context:

```text ignore
Sqlx(RowNotFound)

Caused by:
  0: loading user id 1
  1: authentication
```

But it comes at the expense of erasing the underlying error type.

This type erasure is problematic in a few ways:

- if you want to preserve the ability to use your [thiserror] type, it
  forces you to convert all your errors in your [thiserror] type. This
  is particularly easy to forget to do, as [anyhow] will happily accept
  any error.
- if you forget to convert an error into your [thiserror] type and you want
  to have something approximating the match on your [thiserror] type, then
  you need to attempt to downcast all the possible variants of the [thiserror]
  type. In turn, that means you need to add a downcast attempt for any new
  variants you add to your [thiserror] type. This introduces an easy thing
  to forget to do.

In a happy case, _if_ you remember to convert _all_ your errors into your [thiserror]
type, then you can downcast directly to the [thiserror] type.

```rust
use anyhow::Context;
use thiserror::Error;

#[derive(Debug, Error)]
enum ThisError {
    #[error("placeholder err")]
    Placeholder,

    #[error("sqlx err: {0}")]
    Sqlx(#[from] sqlx::Error),
}

async fn my_fn() -> anyhow::Result<()> {
    async {
        // Some db query or something
        Err(sqlx::Error::RowNotFound)
    }.await
        .map_err(ThisError::from) // <-------------- Important!
        .context("my_fn")?;
    Ok(())
}

async fn caller() -> anyhow::Result<()> {
    let r: anyhow::Result<()> = my_fn().await;

    if let Err(e) = r {
        // So even though we can't match on an anyhow error
        // match r {
        //     Placeholder => { },
        //     Sqlx(_) => { },
        // }

        // We can downcast it to a ThisError, then match on that
        if let Some(x) = e.downcast_ref::<ThisError>() {
            match x {
                ThisError::Placeholder => {}
                ThisError::Sqlx(_) => {}
            }
        }
    }

    Ok(())
}
```

But, if you forget to convert your error into your [thiserror] type,
then things start to get messy.

```rust
use anyhow::Context;
use thiserror::Error;

#[derive(Debug, Error)]
enum ThisError {
    #[error("placeholder err")]
    Placeholder,

    #[error("sqlx err: {0}")]
    Sqlx(#[from] sqlx::Error),
}

async fn my_fn() -> anyhow::Result<()> {
    async {
        // Some db query or something
        Err(sqlx::Error::RowNotFound)
    }.await
        .context("my_fn")?; // <----------- No intermediary conversion into ThisError
    Ok(())
}

async fn caller() -> anyhow::Result<()> {
    let r: anyhow::Result<()> = my_fn().await;

    if let Err(e) = r {
        // We still can't match on an anyhow error
        // match r {
        //     Placeholder => { },
        //     Sqlx(_) => { },
        // }

        if let Some(x) = e.downcast_ref::<ThisError>() {
            // We forgot to explicitly convert our error,
            // so this will never run
            unreachable!("This will never run");
        }

        // So, to be safe, we can start attempting to downcast
        // all the error types that `ThisError` supports?
        if let Some(x) = e.downcast_ref::<sqlx::Error>() {
            // That's okay if ThisError is relatively small,
            // but it's error prone in that we have to remember
            // to add another downcast attempt for any new
            // error variants that are added to `ThisError`
        }
    }

    Ok(())
}
```

# Solution

This crate bridges the two worlds, allowing you to add context to your [thiserror] type
while preserving the ergonomics and accessibility of the underlying error enum.

This crate is intended to be used with [thiserror] enums, but should work with any error type.

** Example **

```rust
use thiserror::Error;
use error_context::{Context, impl_context};

// A normal, run-of-the-mill thiserror enum
#[derive(Debug, Error)]
enum ThisErrorInner {
    #[error("placeholder err")]
    Placeholder,

    #[error("sqlx err: {0}")]
    Sqlx(#[from] sqlx::Error),
}

// Defines a new type, `ThisErr`, that wraps `ThisErrorInner` and allows
// additional context to be added.
impl_context!(ThisError(ThisErrorInner));

// We are returning the wrapped new type, `ThisError`, instead of the
// underlying `ThisErrorInner`.
async fn my_fn() -> Result<(), ThisError> {
    async {
        // Some db query or something
        Err(sqlx::Error::RowNotFound)
    }.await
        .context("my_fn")?;
    Ok(())
}

async fn caller() -> anyhow::Result<()> {
    let r: Result<(), ThisError> = my_fn().await;

    if let Err(e) = r {
        // We can now match on the error type!
        match e.as_ref() {
            ThisErrorInner::Placeholder => {}
            ThisErrorInner::Sqlx(_) => {}
        }
    }

    Ok(())
}
```

# Usage

Similar to [context], this crate provides a [Context] trait that extends
the [Result] type with two methods: `context` and `with_context`.

[context](Context::context) adds static context to the error, while
[with_context](Context::with_context) adds dynamic context to the error.

```rust
use thiserror::Error;
use error_context::{Context, impl_context};

#[derive(Debug, Error)]
enum ThisErrorInner {
    #[error("placeholder err")]
    Placeholder,
}
impl_context!(ThisError(ThisErrorInner));

fn f(id: i64) -> Result<(), ThisError> {
    Err(ThisErrorInner::Placeholder.into())
}

fn t(id: i64) -> Result<(), ThisError> {
    f(id)
        .context("some static context")
        .with_context(|| format!("for id {}", id))
}

let res = t(1);
assert!(res.is_err());
let err = res.unwrap_err();
let debug_repr = format!("{:#?}", err);
assert_eq!(r#"Placeholder

Caused by:
    0: for id 1
    1: some static context
"#, debug_repr);
```

# Nesting

Context enriched errors can be nested and they will preserve their
context messages when converting from a child error type to a parent.

See [impl_from_carry_context] for more information.
