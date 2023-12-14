use crate::{
    ast::WithSpan,
    error::{Error, ErrorVariant},
};
use std::{borrow::Borrow, collections::BTreeMap, rc::Rc};

#[derive(Debug, Default)]
pub struct Inner<K, V> {
    env: BTreeMap<K, V>,
    prev: Option<Env<K, V>>,
}

#[derive(Debug, Clone, Default)]
pub struct Env<K, V>(Rc<Inner<K, V>>);

impl<K, V> Env<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    pub fn new() -> Self {
        Self(Rc::new(Inner {
            env: BTreeMap::new(),
            prev: None,
        }))
    }

    pub fn last(&self) -> &BTreeMap<K, V> {
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

    pub fn insert(&mut self, name: &WithSpan<K>, value: V) -> Result<(), Error>
    where
        K: Copy + ToString,
    {
        match unsafe { Rc::get_mut_unchecked(&mut self.0) }
            .env
            .insert(name.inner, value)
        {
            Some(_) => Err(name.map(ErrorVariant::DuplicateDefinitions))?,
            None => Ok(()),
        }
    }

    pub fn unchecked_insert(&mut self, name: K, value: V) {
        unsafe { Rc::get_mut_unchecked(&mut self.0) }
            .env
            .insert(name, value);
    }

    pub fn find<Q: ?Sized>(&self, name: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let inner = &self.0;
        inner
            .env
            .get(name)
            .or_else(|| inner.prev.as_ref().and_then(|env| env.find(name)))
    }

    pub fn find_mut<Q: ?Sized>(&mut self, name: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let inner = unsafe { Rc::get_mut_unchecked(&mut self.0) };
        inner
            .env
            .get_mut(name)
            .or_else(|| inner.prev.as_mut().and_then(|env| env.find_mut(name)))
    }
}

impl<V> Env<&str, V>
where
    V: Clone,
{
    pub fn get(&self, name: &WithSpan<&str>) -> Result<&V, Error> {
        Ok(self
            .find(name.inner)
            .ok_or_else(|| name.map(ErrorVariant::NotDefined))?)
    }
}
