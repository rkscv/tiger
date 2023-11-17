use crate::{
    ast::WithSpan,
    error::{Error, ErrorVariant},
};
use std::{borrow::Borrow, collections::BTreeMap, rc::Rc};

#[derive(Debug, Default)]
pub struct Inner<'a, V> {
    env: BTreeMap<&'a str, V>,
    prev: Option<Env<'a, V>>,
}

#[derive(Debug, Clone, Default)]
pub struct Env<'a, V>(Rc<Inner<'a, V>>);

impl<'a, V> Env<'a, V>
where
    V: Clone,
{
    pub fn new() -> Self {
        Self(Rc::new(Inner {
            env: BTreeMap::new(),
            prev: None,
        }))
    }

    pub fn last(&self) -> &BTreeMap<&'a str, V> {
        &self.0.env
    }

    pub fn push(&mut self) {
        self.0 = Rc::new(Inner {
            env: BTreeMap::new(),
            prev: Some(self.clone()),
        });
    }

    pub fn pop(&mut self) {
        self.0 = self.0.prev.clone().unwrap().0;
    }

    pub fn insert(&mut self, name: &WithSpan<&'a str>, value: V) -> Result<(), Error> {
        match unsafe { Rc::get_mut_unchecked(&mut self.0) }
            .env
            .insert(name, value)
        {
            Some(_) => Err(name.map(ErrorVariant::DuplicateDefinitions))?,
            None => Ok(()),
        }
    }

    pub fn unchecked_insert(&mut self, name: &'a str, value: V) {
        unsafe { Rc::get_mut_unchecked(&mut self.0) }
            .env
            .insert(name, value);
    }

    pub fn get<I>(&self, name: &WithSpan<I>) -> Result<&V, Error>
    where
        I: Borrow<str> + ToString,
    {
        get_from_env(name, self)
    }

    pub fn get_mut<I>(&mut self, name: &WithSpan<I>) -> Result<&mut V, Error>
    where
        I: Borrow<str> + ToString,
    {
        get_mut_from_env(name, self)
    }
}

fn get_from_env<'a, V, I>(name: &WithSpan<I>, env: &'a Env<'a, V>) -> Result<&'a V, Error>
where
    I: Borrow<str> + ToString,
{
    let inner = &env.0;
    match inner.env.get(name.inner.borrow()) {
        Some(value) => Ok(value),
        None => match &inner.prev {
            Some(env) => get_from_env(name, env),
            None => Err(name.map(ErrorVariant::NotDefined))?,
        },
    }
}

fn get_mut_from_env<'a, V, I>(
    name: &WithSpan<I>,
    env: &'a mut Env<'_, V>,
) -> Result<&'a mut V, Error>
where
    I: Borrow<str> + ToString,
{
    let inner = unsafe { Rc::get_mut_unchecked(&mut env.0) };
    match inner.env.get_mut(name.inner.borrow()) {
        Some(value) => Ok(value),
        None => match &mut inner.prev {
            Some(env) => get_mut_from_env(name, env),
            None => Err(name.map(ErrorVariant::NotDefined))?,
        },
    }
}
