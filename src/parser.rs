use crate::{
    ast::{
        Access, ArcType, Decl, Expr, Field, LValue, Op, Span, Type, WithSpan, INT, STRING, UNIT,
    },
    env::Env,
    error::{Error, ErrorVariant},
};
use paste::paste;
use pest::{iterators::Pair, pratt_parser::PrattParser, Parser};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[derive(Parser)]
#[grammar = "tiger.pest"]
struct TigerParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(or, Left))
            .op(Op::infix(and, Left))
            .op(Op::infix(gt, Left)
                | Op::infix(ge, Left)
                | Op::infix(lt, Left)
                | Op::infix(le, Left)
                | Op::infix(ne, Left)
                | Op::infix(eq, Left))
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
            .op(Op::prefix(minus))
    };
}

fn parse_fields(pair: Pair<Rule>) -> Result<Vec<Field>, Error> {
    let mut pairs = pair.into_inner();
    let mut fields = Vec::new();
    let mut names = HashSet::new();
    while let Some(field) = pairs.next() {
        if !names.insert(field.as_str()) {
            Err(WithSpan {
                span: (&field).into(),
                inner: ErrorVariant::DuplicateDefinitions(field.to_string()),
            })?;
        }
        fields.push(Field {
            name: field.as_str(),
            ty: pairs.next().unwrap().into(),
        });
    }
    Ok(fields)
}

struct Envs<'a> {
    tenv: Env<'a, ArcType<'a>>,
    venv: Env<'a, ArcType<'a>>,
}

impl<'a> Envs<'a> {
    pub fn new() -> Self {
        let mut tenv = Env::new();
        let mut venv = Env::new();

        tenv.unchecked_insert("int", INT.clone());
        tenv.unchecked_insert("string", STRING.clone());

        macro_rules! fun {
            ( $name:expr, ( $( $param_ty:ident ),* ) => $ret_ty:ident ) => {
                paste! {
                    venv.unchecked_insert(
                        stringify!($name),
                        Type::Fun {
                            fields: Vec::from([$([<$param_ty:upper>].clone()),*]),
                            ret_ty: [<$ret_ty:upper>].clone(),
                        }
                        .into(),
                    )
                }
            };
        }
        fun!(print, (string) => unit);
        fun!(flush, () => unit);
        fun!(getchar, () => string);
        fun!(ord, (string) => int);
        fun!(chr, (int) => string);
        fun!(size, (string) => int);
        fun!(substring, (string, int, int) => string);
        fun!(concat, (string, string) => string);
        fun!(not, (int) => int);
        fun!(exit, (int) => unit);

        Self { tenv, venv }
    }

    fn check_ty_decls(&mut self) -> Result<(), Error> {
        let mut traces: HashMap<_, HashSet<_>> = HashMap::new();
        'a: loop {
            for (&name, ty) in self.tenv.last() {
                if let Type::Unknown(ty) = &**ty {
                    if !traces.entry(name).or_default().insert(ty.inner) {
                        return Err(ty.map(ErrorVariant::RecursiveType))?;
                    } else if let Ok(ty) = self.tenv.get(ty).cloned() {
                        self.tenv.unchecked_insert(name, ty);
                    }
                    continue 'a;
                }
            }
            break;
        }
        for ty in self.tenv.last().values() {
            match *ty.clone() {
                Type::Array { ref mut ty, .. } => {
                    if let Type::Unknown(t) = &**ty {
                        *ty = self.tenv.get(t).cloned()?;
                    }
                }
                Type::Record { ref mut fields, .. } => {
                    for (_, ty) in fields {
                        if let Type::Unknown(t) = &**ty {
                            *ty = self.tenv.get(t).cloned()?;
                        }
                    }
                }
                Type::Unknown(_) => unreachable!(),
                Type::Fun { .. } => unreachable!(),
                _ => (),
            }
        }
        Ok(())
    }

    fn check_fun_decls(&mut self, decls: &mut [Decl<'a>]) -> Result<(), Error> {
        for decl in decls {
            if let Decl::Fun {
                fields,
                ret_ty,
                raw_body,
                body,
                ..
            } = decl
            {
                self.venv.push();
                for field in fields {
                    self.venv
                        .unchecked_insert(field.name, self.tenv.get(&field.ty)?.clone());
                }
                let expr = self.parse_with_span(raw_body.take().unwrap(), false)?;
                expr.expect(ret_ty)?;
                *body = Some(expr.inner.into());
                self.venv.pop();
            }
        }
        Ok(())
    }

    fn parse_lvalue(&mut self, pair: Pair<'a, Rule>, breakable: bool) -> Result<LValue<'a>, Error> {
        let mut pairs = pair.into_inner();
        let var = pairs.next().unwrap().into();
        let mut lvalue = LValue {
            ty: self.venv.get(&var)?.clone(),
            access: Access::Var(var),
        };
        for suffix in pairs {
            lvalue = match suffix.as_rule() {
                Rule::record_access => {
                    let field: WithSpan<_> = suffix.into_inner().next().unwrap().into();
                    let Type::Record { fields, .. } = &*lvalue.ty else {
                        return Err(var.with_inner(lvalue).map(ErrorVariant::NotRecord))?;
                    };
                    let (offset, (_, ty)) = fields
                        .iter()
                        .enumerate()
                        .find(|(_, (f, _))| *f == *field)
                        .ok_or_else(|| field.map(ErrorVariant::NoSuchField))?;
                    LValue {
                        ty: ty.clone(),
                        access: Access::Field(lvalue.into(), field, offset),
                    }
                }
                Rule::array_access => LValue {
                    ty: match &*lvalue.ty {
                        Type::Array { ty, .. } => ty.clone(),
                        _ => return Err(var.with_inner(lvalue).map(ErrorVariant::NotArray))?,
                    },
                    access: {
                        let index =
                            self.parse_with_span(suffix.into_inner().next().unwrap(), breakable)?;
                        index.expect(&INT)?;
                        Access::Index(lvalue.into(), index.into())
                    },
                },
                _ => unreachable!(),
            };
        }
        Ok(lvalue)
    }

    fn parse_seq(&mut self, pair: Pair<'a, Rule>, breakable: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Seq(
            pair.into_inner()
                .map(|pair| self.parse(pair, breakable))
                .try_collect()?,
        ))
    }

    fn parse(&mut self, pair: Pair<'a, Rule>, breakable: bool) -> Result<Expr<'a>, Error> {
        match pair.as_rule() {
            Rule::expr => Ok(PRATT_PARSER
                .map_primary(|pair| self.parse_with_span(pair, breakable))
                .map_infix(|lhs, op, rhs| {
                    let lhs = lhs?;
                    let rhs = rhs?;
                    let span = (&op).into();
                    let op = match op.as_rule() {
                        Rule::add => Op::Add,
                        Rule::sub => Op::Sub,
                        Rule::mul => Op::Mul,
                        Rule::div => Op::Div,
                        Rule::gt => Op::Gt,
                        Rule::ge => Op::Ge,
                        Rule::lt => Op::Lt,
                        Rule::le => Op::Le,
                        Rule::ne => Op::Ne,
                        Rule::eq => Op::Eq,
                        Rule::and => Op::And,
                        Rule::or => Op::Or,
                        _ => unreachable!(),
                    };
                    let lty = lhs.ty();
                    let rty = rhs.ty();
                    match (op, &**lty, &**rty) {
                        (
                            Op::Gt | Op::Ge | Op::Lt | Op::Le | Op::Ne | Op::Eq,
                            Type::String,
                            Type::String,
                        )
                        | (_, Type::Int, Type::Int)
                        | (Op::Ne | Op::Eq, Type::Array { .. }, Type::Array { .. })
                        | (Op::Ne | Op::Eq, Type::Array { .. }, Type::Nil)
                        | (Op::Ne | Op::Eq, Type::Nil, Type::Array { .. })
                        | (Op::Ne | Op::Eq, Type::Record { .. }, Type::Record { .. })
                        | (Op::Ne | Op::Eq, Type::Record { .. }, Type::Nil)
                        | (Op::Ne | Op::Eq, Type::Nil, Type::Record { .. }) => Ok(WithSpan {
                            span: Span(lhs.span.0, rhs.span.1),
                            inner: Expr::BinOp {
                                lhs: lhs.inner.into(),
                                rhs: rhs.inner.into(),
                                op: WithSpan { span, inner: op },
                            },
                        }),
                        _ => Err(WithSpan {
                            span,
                            inner: ErrorVariant::UnsupportedOperandTypes {
                                op,
                                lty: lty.to_string(),
                                rty: rty.to_string(),
                            },
                        })?,
                    }
                })
                .map_prefix(|op, expr| match op.as_rule() {
                    Rule::minus => {
                        let expr = expr?;
                        expr.expect(&INT)?;
                        Ok(WithSpan {
                            span: Span(op.as_span().start(), expr.span.1),
                            inner: Expr::Neg(expr.inner.into()),
                        })
                    }
                    _ => unreachable!(),
                })
                .parse(pair.into_inner())?
                .inner),
            Rule::lvalue => Ok(Expr::LValue(self.parse_lvalue(pair, breakable)?)),
            Rule::nil => Ok(Expr::Nil),
            Rule::seq => self.parse_seq(pair, breakable),
            Rule::int => Ok(Expr::Int(pair.as_str().parse().map_err(|error| {
                WithSpan {
                    span: (&pair).into(),
                    inner: ErrorVariant::ParseIntError(error),
                }
            })?)),
            Rule::string => {
                let s = pair.as_str();
                let s = &s[1..s.len() - 1];
                let mut string = String::new();
                let mut has_escape_char = false;
                for pair in pair.into_inner() {
                    let mut escape = true;
                    match pair.as_rule() {
                        Rule::newline => string.push('\n'),
                        Rule::tab => string.push('\t'),
                        Rule::ctrl => {
                            string.push(char::from(match pair.as_str().bytes().last().unwrap() {
                                ctrl @ b'A'..=b'_' => ctrl - b'A' + 1,
                                b'?' => 127,
                                _ => unreachable!(),
                            }))
                        }
                        Rule::decimal => string.push(
                            char::try_from(pair.as_str()[1..].parse::<u32>().unwrap()).unwrap(),
                        ),
                        Rule::quotmark => string.push('"'),
                        Rule::backslash => string.push('\\'),
                        Rule::ignore => (),
                        Rule::char => {
                            escape = false;
                            string.push_str(pair.as_str())
                        }
                        _ => unreachable!(),
                    }
                    has_escape_char |= escape;
                }
                Ok(Expr::String(if has_escape_char {
                    Cow::Owned(string)
                } else {
                    Cow::Borrowed(s)
                }))
            }
            Rule::call => {
                let mut pairs = pair.into_inner();
                let name = pairs.next().unwrap().into();
                let args = pairs
                    .map(|pair| self.parse_with_span(pair, breakable))
                    .try_collect::<Vec<_>>()?;
                let Type::Fun { fields, ret_ty } = &**self.venv.get(&name)? else {
                    return Err(name.map(ErrorVariant::NotCallable))?;
                };
                if fields.len() != args.len() {
                    return Err(name.with_inner(ErrorVariant::MismatchedArgumentNum {
                        name: name.to_string(),
                        expected: fields.len(),
                        found: args.len(),
                    }))?;
                }
                for (field, arg) in fields.iter().zip(args.iter()) {
                    arg.expect(field)?;
                }
                Ok(Expr::Call {
                    name,
                    args,
                    ret_ty: ret_ty.clone(),
                })
            }
            Rule::record => {
                let mut pairs = pair.into_inner();
                let t = pairs.next().unwrap().into();
                let ty = self.tenv.get(&t)?.clone();
                let Type::Record { fields, .. } = &*ty else {
                    return Err(t.map(ErrorVariant::NotRecord))?;
                };
                let mut fields = fields.iter();
                let mut exprs = Vec::new();
                while let Some(field) = pairs.next() {
                    let expr = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                    expr.expect(match fields.next() {
                        Some((f, ty)) if *f == field.as_str() => ty,
                        _ => return Err(WithSpan::from(field).map(ErrorVariant::UnexpectedField))?,
                    })?;
                    exprs.push(expr.inner);
                }
                if let Some((field, _)) = fields.next() {
                    return Err(t.with_inner(ErrorVariant::UninitializedField(field.to_string())))?;
                }
                Ok(Expr::Record { fields: exprs, ty })
            }
            Rule::array => {
                let mut pairs = pair.into_inner();
                let t = pairs.next().unwrap().into();
                let n = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                n.expect(&INT)?;
                let v = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                let ty = self.tenv.get(&t)?;
                v.expect(match &**ty {
                    Type::Array { ty, .. } => ty,
                    _ => return Err(t.map(ErrorVariant::NotArray))?,
                })?;
                Ok(Expr::Array {
                    n: n.into(),
                    v: v.inner.into(),
                    ty: ty.clone(),
                })
            }
            Rule::assign => {
                let mut pairs = pair.into_inner();
                let lvalue = self.parse_lvalue(pairs.next().unwrap(), breakable)?;
                let expr = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                expr.expect(&lvalue.ty)?;
                Ok(Expr::Assign {
                    lvalue,
                    expr: expr.inner.into(),
                })
            }
            Rule::r#if => {
                let mut pairs = pair.into_inner();
                let cond = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                cond.expect(&INT)?;
                let t = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                Ok(match pairs.next() {
                    Some(pair) => {
                        let f = self.parse_with_span(pair, breakable)?;
                        f.expect(t.ty())?;
                        Expr::If {
                            cond: cond.inner.into(),
                            t: t.inner.into(),
                            f: Some(f.inner.into()),
                        }
                    }
                    None => {
                        t.expect(&UNIT)?;
                        Expr::If {
                            cond: cond.inner.into(),
                            t: t.inner.into(),
                            f: None,
                        }
                    }
                })
            }
            Rule::r#while => {
                let mut pairs = pair.into_inner();
                let cond = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                cond.expect(&INT)?;
                let body = self.parse_with_span(pairs.next().unwrap(), true)?;
                body.expect(&UNIT)?;
                Ok(Expr::While {
                    cond: cond.inner.into(),
                    body: body.inner.into(),
                })
            }
            Rule::r#for => {
                let mut pairs = pair.into_inner();
                let name = pairs.next().unwrap().as_str();
                let begin = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                begin.expect(&INT)?;
                let end = self.parse_with_span(pairs.next().unwrap(), breakable)?;
                end.expect(&INT)?;
                self.venv.push();
                self.venv.unchecked_insert(name, INT.clone());
                let body = self.parse_with_span(pairs.next().unwrap(), true)?;
                body.expect(&UNIT)?;
                self.venv.pop();
                Ok(Expr::For {
                    name,
                    begin: begin.inner.into(),
                    end: end.inner.into(),
                    body: body.inner.into(),
                })
            }
            Rule::r#break => {
                if breakable {
                    Ok(Expr::Break)
                } else {
                    Err(WithSpan {
                        span: (&pair).into(),
                        inner: ErrorVariant::BreakOutsideLoop,
                    })?
                }
            }
            Rule::r#let => {
                #[derive(Clone, Copy, PartialEq)]
                enum DeclType {
                    Ty,
                    Var,
                    Fun,
                }
                let mut decls: Vec<Vec<_>> = Vec::new();
                let mut pairs = pair.into_inner().peekable();
                let mut last = None;
                let mut venv = 0usize;
                let mut tenv = 0usize;
                while let Some(pair) = pairs.next() {
                    if pairs.peek().is_none() {
                        match last {
                            Some(DeclType::Ty) => self.check_ty_decls()?,
                            Some(DeclType::Fun) => {
                                self.check_fun_decls(decls.last_mut().unwrap())?
                            }
                            _ => (),
                        }
                        let expr = self.parse_seq(pair, breakable)?.into();
                        for _ in 0..venv {
                            self.venv.pop();
                        }
                        for _ in 0..tenv {
                            self.tenv.pop();
                        }
                        return Ok(Expr::Let { expr, decls });
                    }
                    match pair.as_rule() {
                        Rule::ty_decl => {
                            let last = last.replace(DeclType::Ty);
                            if last != Some(DeclType::Ty) {
                                if let Some(DeclType::Fun) = last {
                                    self.check_fun_decls(decls.last_mut().unwrap())?;
                                }
                                self.tenv.push();
                                tenv += 1;
                            }
                            let mut pairs = pair.into_inner();
                            let name = pairs.next().unwrap().into();
                            let ty = pairs.next().unwrap();
                            let get = |ty: WithSpan<&'a str>| {
                                self.tenv
                                    .get(&ty)
                                    .cloned()
                                    .unwrap_or_else(|_| Type::Unknown(ty).into())
                            };
                            self.tenv.insert(
                                &name,
                                match ty.as_rule() {
                                    Rule::ident => get(ty.into()),
                                    Rule::array_ty => Type::Array {
                                        name: &name,
                                        ty: get(ty.into_inner().next().unwrap().into()),
                                    }
                                    .into(),
                                    Rule::record_ty => Type::Record {
                                        name: &name,
                                        fields: parse_fields(ty.into_inner().next().unwrap())?
                                            .into_iter()
                                            .map(|field| (field.name, get(field.ty)))
                                            .collect(),
                                    }
                                    .into(),
                                    _ => unreachable!(),
                                },
                            )?;
                        }
                        Rule::var_decl => {
                            let last = last.replace(DeclType::Var);
                            if last != Some(DeclType::Var) {
                                match last {
                                    Some(DeclType::Fun) => {
                                        self.check_fun_decls(decls.last_mut().unwrap())?
                                    }
                                    Some(DeclType::Ty) => self.check_ty_decls()?,
                                    _ => (),
                                }
                                decls.push(Vec::new());
                                self.venv.push();
                                venv += 1;
                            }
                            let mut pairs = pair.into_inner();
                            let name: WithSpan<_> = pairs.next().unwrap().into();
                            let pair = pairs.next().unwrap();
                            decls.last_mut().unwrap().push(Decl::Var {
                                name: name.inner,
                                expr: match pair.as_rule() {
                                    Rule::ident => {
                                        let expr =
                                            self.parse_with_span(pairs.next().unwrap(), breakable)?;
                                        let ty = self.tenv.get(&pair.into())?;
                                        expr.expect(ty)?;
                                        self.venv.unchecked_insert(&name, ty.clone());
                                        expr.inner.into()
                                    }
                                    Rule::expr => {
                                        let expr = self.parse_with_span(pair, breakable)?;
                                        let ty = expr.ty();
                                        if let Type::Nil = &**ty {
                                            return Err(name.map(ErrorVariant::UnknownType))?;
                                        }
                                        self.venv.unchecked_insert(&name, ty.clone());
                                        expr.inner.into()
                                    }
                                    _ => unreachable!(),
                                },
                            });
                        }
                        Rule::fun_decl => {
                            let last = last.replace(DeclType::Fun);
                            if last != Some(DeclType::Fun) {
                                if let Some(DeclType::Ty) = last {
                                    self.check_ty_decls()?;
                                }
                                decls.push(Vec::new());
                                self.venv.push();
                                venv += 1;
                            }
                            let mut pairs = pair.into_inner();
                            let name = pairs.next().unwrap().into();
                            let fields = parse_fields(pairs.next().unwrap())?;
                            let pair = pairs.next().unwrap();
                            let (ret_ty, raw_body) = match pair.as_rule() {
                                Rule::ident => {
                                    (self.tenv.get(&pair.into())?.clone(), pairs.next().unwrap())
                                }
                                Rule::expr => (UNIT.clone(), pair),
                                _ => unreachable!(),
                            };
                            self.venv.insert(
                                &name,
                                Type::Fun {
                                    ret_ty: ret_ty.clone(),
                                    fields: fields
                                        .iter()
                                        .map(|field| self.tenv.get(&field.ty).cloned())
                                        .try_collect()?,
                                }
                                .into(),
                            )?;
                            decls.last_mut().unwrap().push(Decl::Fun {
                                name: name.inner,
                                fields,
                                ret_ty,
                                raw_body: Some(raw_body),
                                body: None,
                            });
                        }
                        _ => unreachable!(),
                    };
                }
                Ok(Expr::Let {
                    decls,
                    expr: Expr::Seq(Vec::new()).into(),
                })
            }
            _ => unreachable!("{:?}", pair.as_rule()),
        }
    }

    fn parse_with_span(
        &mut self,
        pair: Pair<'a, Rule>,
        breakable: bool,
    ) -> Result<WithSpan<Expr<'a>>, Error> {
        Ok(WithSpan {
            span: (&pair).into(),
            inner: self.parse(pair, breakable)?,
        })
    }
}

pub fn parse(src: &str) -> Result<Expr, Error> {
    Envs::new().parse(
        TigerParser::parse(Rule::main, src)
            .map_err(Box::new)
            .map_err(Error::ParseError)?
            .next()
            .unwrap()
            .into_inner()
            .next()
            .unwrap(),
        false,
    )
}
