use crate::{
    ast::{Access, Decl, Expr, LValue, Op, WithSpan},
    env::Env,
    error::{Error, ErrorVariant},
};
use std::{
    borrow::Cow,
    fmt::Debug,
    io::{Read, Write},
    iter::once,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub enum Value<'a> {
    Unit,
    Nil,
    Int(isize),
    String(Cow<'a, str>),
    Array(Rc<Vec<Self>>),
    Record(Rc<Vec<Self>>),

    Print,
    Flush,
    GetChar,
    Ord,
    Chr,
    Size,
    SubString,
    Concat,
    Not,
    Exit,
    Fun {
        fields: Rc<Vec<&'a str>>,
        body: Rc<Expr<'a>>,
        venv: Env<&'a str, Self>,
    },
}

impl<'a> Value<'a> {
    fn int(self) -> isize {
        match self {
            Value::Int(int) => int,
            _ => unreachable!(),
        }
    }

    fn string(self) -> Cow<'a, str> {
        match self {
            Value::String(string) => string,
            _ => unreachable!(),
        }
    }
}

impl WithSpan<Value<'_>> {
    fn index(self) -> Result<usize, Error> {
        match *self {
            Value::Int(int) => Ok(usize::try_from(int)
                .map_err(|_| self.with_inner(ErrorVariant::NegtiveIndex(int)))?),
            _ => unreachable!(),
        }
    }
}

struct VM<'a> {
    venv: Env<&'a str, Value<'a>>,
}

impl<'a> VM<'a> {
    fn new() -> Self {
        let mut venv = Env::new();
        venv.unchecked_insert("print", Value::Print);
        venv.unchecked_insert("flush", Value::Flush);
        venv.unchecked_insert("getchar", Value::GetChar);
        venv.unchecked_insert("ord", Value::Ord);
        venv.unchecked_insert("chr", Value::Chr);
        venv.unchecked_insert("size", Value::Size);
        venv.unchecked_insert("substring", Value::SubString);
        venv.unchecked_insert("concat", Value::Concat);
        venv.unchecked_insert("not", Value::Not);
        venv.unchecked_insert("exit", Value::Exit);
        Self { venv }
    }

    fn eval_lvalue(&mut self, lvalue: &LValue<'a>) -> Result<&mut Value<'a>, Error> {
        match &lvalue.access {
            Access::Var(var) => Ok(self.venv.get_mut(var).unwrap()),
            Access::Field(lvalue, field, offset) => match self.eval_lvalue(lvalue)? {
                Value::Record(fields) => Ok(unsafe { Rc::get_mut_unchecked(fields) }
                    .get_mut(*offset)
                    .unwrap()),
                Value::Nil => Err(field.with_inner(ErrorVariant::DerefNilRecord))?,
                _ => unreachable!(),
            },
            Access::Index(lvalue, index) => {
                let i = self.eval_with_span(index)?.index()?;
                match self.eval_lvalue(lvalue)? {
                    Value::Array(array) => {
                        Ok(unsafe { Rc::get_mut_unchecked(array) }
                            .get_mut(i)
                            .ok_or_else(|| index.with_inner(ErrorVariant::IndexOutOfRange(i)))?)
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn eval_decls(&mut self, decls: &Vec<Vec<Decl<'a>>>) -> Result<(), Error> {
        for batch in decls {
            self.venv.push();
            for decl in batch {
                match decl {
                    Decl::Var { name, expr, .. } => {
                        let value = self.eval(expr)?;
                        self.venv.unchecked_insert(name, value);
                    }
                    Decl::Fun {
                        name, fields, body, ..
                    } => {
                        self.venv.unchecked_insert(
                            name,
                            Value::Fun {
                                fields: fields
                                    .iter()
                                    .map(|field| field.name)
                                    .collect::<Vec<_>>()
                                    .into(),
                                body: body.clone().unwrap(),
                                venv: self.venv.clone(),
                            },
                        );
                    }
                }
            }
        }
        Ok(())
    }

    fn eval(&mut self, expr: &Expr<'a>) -> Result<Value<'a>, Error> {
        match expr {
            Expr::BinOp {
                lhs,
                rhs,
                op: WithSpan { inner: op, span },
            } => Ok(Value::Int(match op {
                Op::And => match self.eval(lhs)?.int() {
                    0 => 0,
                    _ => (self.eval(rhs)?.int() != 0) as isize,
                },
                Op::Or => match self.eval(lhs)?.int() {
                    0 => (self.eval(rhs)?.int() != 0) as isize,
                    _ => 1,
                },
                op => {
                    let lhs = self.eval(lhs)?;
                    let rhs = self.eval(rhs)?;
                    match (lhs, rhs, op) {
                        (Value::Nil, Value::Nil, Op::Eq) => 1,
                        (Value::Nil, Value::Nil, Op::Ne) => 0,
                        (Value::Record(_), Value::Nil, Op::Eq) => 0,
                        (Value::Record(_), Value::Nil, Op::Ne) => 1,
                        (Value::Nil, Value::Record(_), Op::Eq) => 0,
                        (Value::Nil, Value::Record(_), Op::Ne) => 1,
                        (Value::Record(lhs), Value::Record(rhs), Op::Eq) => {
                            Rc::ptr_eq(&lhs, &rhs) as isize
                        }
                        (Value::Record(lhs), Value::Record(rhs), Op::Ne) => {
                            !Rc::ptr_eq(&lhs, &rhs) as isize
                        }

                        (Value::String(lhs), Value::String(rhs), Op::Gt) => (lhs > rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Ge) => (lhs >= rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Lt) => (lhs < rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Le) => (lhs <= rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Eq) => (lhs == rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Ne) => (lhs != rhs) as isize,

                        (Value::Int(lhs), Value::Int(rhs), Op::Gt) => (lhs > rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Ge) => (lhs >= rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Lt) => (lhs < rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Le) => (lhs <= rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Eq) => (lhs == rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Ne) => (lhs != rhs) as isize,
                        (Value::Int(lhs), Value::Int(rhs), Op::Add) => lhs + rhs,
                        (Value::Int(lhs), Value::Int(rhs), Op::Sub) => lhs - rhs,
                        (Value::Int(lhs), Value::Int(rhs), Op::Mul) => lhs * rhs,
                        (Value::Int(lhs), Value::Int(rhs), Op::Div) => {
                            if rhs == 0 {
                                return Err(WithSpan {
                                    span: *span,
                                    inner: ErrorVariant::DivideByZero,
                                })?;
                            }
                            lhs / rhs
                        }
                        _ => unreachable!(),
                    }
                }
            })),
            Expr::Nil => Ok(Value::Nil),
            Expr::Neg(expr) => Ok(Value::Int(-self.eval(expr)?.int())),
            Expr::Seq(exprs) => match &exprs[..] {
                [] => Ok(Value::Unit),
                [exprs @ .., expr] => {
                    for expr in exprs {
                        self.eval(expr)?;
                    }
                    self.eval(expr)
                }
            },
            Expr::Int(int) => Ok(Value::Int(*int)),
            Expr::String(string) => Ok(Value::String(string.clone())),
            Expr::If { cond, t, f } => {
                let cond = self.eval(cond)?.int();
                match f {
                    Some(f) => self.eval(if cond == 0 { f } else { t }),
                    None => {
                        if cond != 0 {
                            self.eval(t)?;
                        }
                        Ok(Value::Unit)
                    }
                }
            }
            Expr::While { cond, body } => {
                while self.eval(cond)?.int() != 0 {
                    match self.eval(body) {
                        Err(Error::Break) => break,
                        other => other?,
                    };
                }
                Ok(Value::Unit)
            }
            Expr::For {
                name,
                begin,
                end,
                body,
            } => {
                let begin = self.eval(begin)?.int();
                let end = self.eval(end)?.int();
                self.venv.push();
                for i in begin..=end {
                    self.venv.unchecked_insert(name, Value::Int(i));
                    match self.eval(body) {
                        Err(Error::Break) => break,
                        other => other?,
                    };
                }
                self.venv.pop();
                Ok(Value::Unit)
            }
            Expr::Break => Err(Error::Break),
            Expr::Let { decls, expr } => {
                self.eval_decls(decls)?;
                let value = self.eval(expr)?;
                for _ in decls {
                    self.venv.pop();
                }
                Ok(value)
            }
            Expr::Call { name, args, .. } => {
                let fun = self.venv.get(name).unwrap().clone();
                let mut args = args.iter();
                match fun {
                    Value::Print => {
                        print!("{}", self.eval(args.next().unwrap())?.string());
                        Ok(Value::Unit)
                    }
                    Value::Flush => {
                        std::io::stdout()
                            .flush()
                            .map_err(|error| name.with_inner(ErrorVariant::IOError(error)))?;
                        Ok(Value::Unit)
                    }
                    Value::GetChar => {
                        let mut buf = [0u8];
                        Ok(Value::String(
                            if std::io::stdin()
                                .read(&mut buf[..])
                                .map_err(|error| name.with_inner(ErrorVariant::IOError(error)))?
                                == 0
                            {
                                Cow::Borrowed("")
                            } else {
                                Cow::Owned(String::from(char::from(buf[0])))
                            },
                        ))
                    }
                    Value::Ord => Ok(Value::Int(
                        self.eval(args.next().unwrap())?
                            .string()
                            .bytes()
                            .next()
                            .map(From::from)
                            .unwrap_or(-1),
                    )),
                    Value::Chr => Ok(Value::String(Cow::Owned(String::from(char::from(
                        u8::try_from(self.eval(args.next().unwrap())?.int()).map_err(|error| {
                            name.with_inner(ErrorVariant::TryFromIntError(error))
                        })?,
                    ))))),
                    Value::Size => Ok(Value::Int(
                        self.eval(args.next().unwrap())?
                            .string()
                            .len()
                            .try_into()
                            .map_err(|error| {
                                name.with_inner(ErrorVariant::TryFromIntError(error))
                            })?,
                    )),
                    Value::SubString => {
                        let s = self.eval(args.next().unwrap())?.string();
                        let first = self.eval_with_span(args.next().unwrap())?.index()?;
                        let n = self.eval_with_span(args.next().unwrap())?.index()?;
                        let slice = first..first + n;
                        Ok(Value::String(match s {
                            Cow::Borrowed(s) => Cow::Borrowed(s.get(slice).unwrap_or_default()),
                            Cow::Owned(s) => Cow::Owned(s.get(slice).unwrap_or_default().into()),
                        }))
                    }
                    Value::Concat => {
                        let mut s1 = self.eval(args.next().unwrap())?.string().to_string();
                        let s2 = self.eval(args.next().unwrap())?.string();
                        s1.push_str(&s2);
                        Ok(Value::String(Cow::Owned(s1)))
                    }
                    Value::Not => Ok(Value::Int(isize::from(
                        self.eval(args.next().unwrap())?.int() == 0,
                    ))),
                    Value::Exit => std::process::exit(
                        self.eval(args.next().unwrap())?
                            .int()
                            .try_into()
                            .map_err(|error| {
                                name.with_inner(ErrorVariant::TryFromIntError(error))
                            })?,
                    ),
                    Value::Fun {
                        fields,
                        body,
                        mut venv,
                    } => {
                        venv.push();
                        for (param, arg) in fields.iter().zip(args) {
                            venv.unchecked_insert(param, self.eval(arg)?);
                        }
                        VM { venv }.eval(&body)
                    }
                    _ => unreachable!(),
                }
            }
            Expr::Record { fields, .. } => Ok(Value::Record(Rc::new(
                fields.iter().map(|field| self.eval(field)).try_collect()?,
            ))),
            Expr::Array { n, v, .. } => {
                let n = self.eval_with_span(n)?.index()?;
                let v = self.eval(v)?;
                Ok(Value::Array(Rc::new(once(v).cycle().take(n).collect())))
            }
            Expr::Assign { lvalue, expr } => {
                *self.eval_lvalue(lvalue)? = self.eval(expr)?;
                Ok(Value::Unit)
            }
            Expr::LValue(lvalue) => self.eval_lvalue(lvalue).cloned(),
        }
    }

    fn eval_with_span(&mut self, expr: &WithSpan<Expr<'a>>) -> Result<WithSpan<Value<'a>>, Error> {
        Ok(expr.with_inner(self.eval(expr)?))
    }
}

pub fn eval<'a>(expr: &'a Expr) -> Result<Value<'a>, Error> {
    VM::new().eval(expr)
}
