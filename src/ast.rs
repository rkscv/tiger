use crate::{
    error::{Error, ErrorVariant},
    parser::Rule,
};
use lazy_static::lazy_static;
use pest::{iterators::Pair, RuleType};
use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::{self, Display, Formatter},
    ops::{Deref, DerefMut, RangeFrom},
    rc::Rc,
    sync::Arc,
};

lazy_static! {
    pub static ref UNIT: ArcType<'static> = Type::Unit.into();
    pub static ref NIL: ArcType<'static> = Type::Nil.into();
    pub static ref INT: ArcType<'static> = Type::Int.into();
    pub static ref STRING: ArcType<'static> = Type::String.into();
}

#[derive(Debug, Clone, Copy)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Gt,
    Ge,
    Lt,
    Le,
    Ne,
    Eq,
    And,
    Or,
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Ne => "!=",
            Self::Eq => "=",
            Self::And => "&",
            Self::Or => "|",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ID(usize);

#[derive(Debug, Clone, Copy)]
pub struct Symbol<'a> {
    pub name: &'a str,
    pub id: ID,
}

pub struct Symbols<'a> {
    symbols: HashMap<&'a str, ID>,
    ids: RangeFrom<usize>,
}

impl<'a> Symbols<'a> {
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            ids: 0..,
        }
    }

    pub fn get(&mut self, name: &'a str) -> Symbol<'a> {
        let id = *self
            .symbols
            .entry(name)
            .or_insert_with(|| ID(self.ids.next().unwrap()));
        Symbol { name, id }
    }
}

impl Default for Symbols<'_> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Field<'a> {
    pub symbol: Symbol<'a>,
    pub ty: WithSpan<&'a str>,
}

#[derive(Debug, Clone)]
pub enum Decl<'a> {
    Var {
        symbol: Symbol<'a>,
        expr: Box<Expr<'a>>,
    },
    Fun {
        symbol: Symbol<'a>,
        fields: Vec<Field<'a>>,
        ret_ty: ArcType<'a>,
        raw_body: Option<Pair<'a, Rule>>,
        body: Option<Rc<Expr<'a>>>,
    },
}

#[derive(Debug, Clone)]
pub enum Access<'a> {
    Var(WithSpan<Symbol<'a>>),
    Field(Box<LValue<'a>>, WithSpan<&'a str>, usize),
    Index(Box<LValue<'a>>, Box<WithSpan<Expr<'a>>>),
}

#[derive(Debug, Clone)]
pub struct LValue<'a> {
    pub access: Access<'a>,
    pub ty: ArcType<'a>,
}

impl Display for LValue<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &self.access {
            Access::Var(var) => f.write_str(var.name),
            Access::Field(lvalue, field, _) => {
                lvalue.fmt(f)?;
                f.write_str(".")?;
                f.write_str(field)
            }
            Access::Index(lvalue, _) => {
                lvalue.fmt(f)?;
                f.write_str("[..]")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Nil,
    Break,
    Int(isize),
    String(Cow<'a, str>),
    Neg(Box<Self>),
    LValue(LValue<'a>),
    Seq(Vec<Self>),
    Record {
        fields: Vec<Self>,
        ty: ArcType<'a>,
    },
    Array {
        n: Box<WithSpan<Self>>,
        v: Box<Self>,
        ty: ArcType<'a>,
    },
    BinOp {
        lhs: Box<Self>,
        rhs: Box<Self>,
        op: WithSpan<Op>,
    },
    If {
        cond: Box<Self>,
        t: Box<Self>,
        f: Option<Box<Self>>,
    },
    While {
        cond: Box<Self>,
        body: Box<Self>,
    },
    For {
        symbol: Symbol<'a>,
        begin: Box<Self>,
        end: Box<Self>,
        body: Box<Self>,
    },
    Let {
        decls: Vec<Vec<Decl<'a>>>,
        expr: Box<Self>,
    },
    Call {
        symbol: WithSpan<Symbol<'a>>,
        args: Vec<WithSpan<Self>>,
        ret_ty: ArcType<'a>,
    },
    Assign {
        lvalue: LValue<'a>,
        expr: Box<Self>,
    },
}

impl<'a> Expr<'a> {
    pub fn ty(&self) -> &ArcType<'a> {
        match self {
            Self::Nil => &NIL,
            Self::String(_) => &STRING,
            Self::Int(_) | Self::Neg(_) | Self::BinOp { .. } => &INT,
            Self::While { .. } | Self::For { .. } | Self::Assign { .. } | Self::Break => &UNIT,
            Self::Seq(exprs) => exprs.last().map(Expr::ty).unwrap_or(&UNIT),
            Self::LValue(LValue { ty, .. }) => ty,
            Self::Record { ty, .. } => ty,
            Self::Array { ty, .. } => ty,
            Self::If { t, f, .. } => match f {
                Some(f) => {
                    let t = t.ty();
                    let f = f.ty();
                    match &**t {
                        Type::Nil => f,
                        _ => t,
                    }
                }
                None => t.ty(),
            },
            Self::Let { expr, .. } => expr.ty(),
            Self::Call { ret_ty, .. } => ret_ty,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ArcType<'a>(Arc<Type<'a>>);

impl Display for ArcType<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(match &*self.0 {
            Type::Unit => "unit",
            Type::Int => "int",
            Type::String => "string",
            Type::Nil => "nil",
            Type::Fun { .. } => "function",
            Type::Array { name, .. } => name,
            Type::Record { name, .. } => name,
            Type::Unknown(_) => unreachable!(),
        })
    }
}

impl<'a> From<Type<'a>> for ArcType<'a> {
    fn from(value: Type<'a>) -> Self {
        Self(Arc::new(value))
    }
}

impl<'a> Deref for ArcType<'a> {
    type Target = Type<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ArcType<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { Arc::get_mut_unchecked(&mut self.0) }
    }
}

impl PartialEq for ArcType<'_> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl WithSpan<Expr<'_>> {
    pub fn expect(&self, expected: &ArcType) -> Result<(), Error> {
        let found = self.ty();
        if found == expected
            || matches!(
                (&**found, &**expected),
                (Type::Record { .. }, Type::Nil) | (Type::Nil, Type::Record { .. })
            )
        {
            Ok(())
        } else {
            Err(self.with_inner(ErrorVariant::MismatchedTypes {
                expected: expected.to_string(),
                found: found.to_string(),
            }))?
        }
    }
}

#[derive(Debug)]
pub enum Type<'a> {
    Unknown(WithSpan<&'a str>),
    Unit,
    Int,
    String,
    Nil,
    Array {
        name: &'a str,
        ty: ArcType<'a>,
    },
    Record {
        name: &'a str,
        fields: Vec<(&'a str, ArcType<'a>)>,
    },
    Fun {
        fields: Vec<ArcType<'a>>,
        ret_ty: ArcType<'a>,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct Span(pub usize, pub usize);

impl<R: RuleType> From<&Pair<'_, R>> for Span {
    fn from(value: &Pair<'_, R>) -> Self {
        let span = value.as_span();
        Self(span.start(), span.end())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct WithSpan<T> {
    pub span: Span,
    pub inner: T,
}

impl<T> WithSpan<T> {
    pub fn with_inner<P>(&self, inner: P) -> WithSpan<P> {
        WithSpan {
            span: self.span,
            inner,
        }
    }
}

impl<T> WithSpan<T>
where
    T: ToString,
{
    pub fn map<V, F>(&self, f: F) -> WithSpan<V>
    where
        F: Fn(String) -> V,
    {
        self.with_inner(f(self.to_string()))
    }
}

impl<T> Deref for WithSpan<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'a, R: RuleType> From<Pair<'a, R>> for WithSpan<&'a str> {
    fn from(value: Pair<'a, R>) -> Self {
        Self {
            span: (&value).into(),
            inner: value.as_str(),
        }
    }
}
