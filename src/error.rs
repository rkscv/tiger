use crate::{
    ast::{Op, Span, WithSpan},
    parser::Rule,
};
use pest::error::InputLocation;
use std::{borrow::Cow, fmt::Debug, io, num};
use thiserror::Error;

#[derive(Debug)]
pub enum Error {
    Variant(WithSpan<ErrorVariant>),
    ParseError(Box<pest::error::Error<Rule>>),
    Break,
}

impl Error {
    pub fn span(&self) -> Span {
        match self {
            Error::Variant(error) => error.span,
            Error::ParseError(error) => match error.location {
                InputLocation::Pos(pos) => Span(pos, pos),
                InputLocation::Span((start, end)) => Span(start, end),
            },
            Error::Break => unreachable!(),
        }
    }

    pub fn message(&self) -> Cow<'_, str> {
        match self {
            Error::Variant(error) => Cow::Owned(error.to_string()),
            Error::ParseError(error) => error.variant.message(),
            Error::Break => unreachable!(),
        }
    }
}

impl From<WithSpan<ErrorVariant>> for Error {
    fn from(error: WithSpan<ErrorVariant>) -> Self {
        Self::Variant(error)
    }
}

#[derive(Error, Debug)]
pub enum ErrorVariant {
    #[error("{0}")]
    ParseIntError(num::ParseIntError),
    #[error("unsupported operand type(s) '{lty}' and '{rty}' for '{op}'")]
    UnsupportedOperandTypes { op: Op, lty: String, rty: String },
    #[error("type mismatch, expected '{expected}', found '{found}'")]
    MismatchedTypes { expected: String, found: String },
    #[error("'{name}' takes {expected} argument(s) but {found} were given")]
    MismatchedArgumentNum {
        name: String,
        expected: usize,
        found: usize,
    },
    #[error("uninitialized field '{0}'")]
    UninitializedField(String),
    #[error("multiple definitions with the same name '{0}'")]
    DuplicateDefinitions(String),
    #[error("recursive type '{0}'")]
    RecursiveType(String),
    #[error("type of '{0}' is unknown")]
    UnknownType(String),
    #[error("name '{0}' is not defined")]
    NotDefined(String),
    #[error("'{0}' is not callable")]
    NotCallable(String),
    #[error("'{0}' is not a record")]
    NotRecord(String),
    #[error("the record has no field '{0}'")]
    NoSuchField(String),
    #[error("unexpected record field '{0}'")]
    UnexpectedField(String),
    #[error("'{0}' is not an array")]
    NotArray(String),
    #[error("break outside loop")]
    BreakOutsideLoop,

    #[error("divide by zero")]
    DivideByZero,
    #[error("nil-valued record dereference")]
    DerefNilRecord,
    #[error("negative index {0}")]
    NegtiveIndex(isize),
    #[error("index {0} out of range")]
    IndexOutOfRange(usize),
    #[error("{0}")]
    IOError(io::Error),
    #[error("{0}")]
    TryFromIntError(num::TryFromIntError),
}
