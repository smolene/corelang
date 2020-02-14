#![allow(dead_code)]

use std::cell::Cell;
use std::marker::PhantomData;
use std::fmt::Debug;
use nom::lib::std::fmt::{Formatter, Error};

#[derive(Copy, Clone)]
pub struct Index<K>(usize, PhantomData<K>);

impl<K> Debug for Index<K> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "'{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct Store<T, K> {
    vec: Vec<T>,
    key_type: PhantomData<K>,
}

impl<T, K> Store<T, K> {
    pub fn new() -> Self {
        Self { vec: vec![], key_type: PhantomData }
    }

    pub fn insert(&mut self, obj: T) -> Index<K> {
        self.vec.push(obj);
        Index(self.vec.len() - 1, PhantomData)
    }

    pub fn lookup(&self, index: Index<K>) -> &T {
        self.vec.get(index.0).unwrap()
    }

    pub fn lookup_mut(&mut self, index: Index<K>) -> &mut T {
        self.vec.get_mut(index.0).unwrap()
    }

    pub fn inner(&self) -> &Vec<T> {
        &self.vec
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Handle<K>(usize, PhantomData<K>);

#[derive(Debug, Clone)]
pub struct GcStore<T, K> {
    store: Vec<T>,
    key_type: PhantomData<K>,
}

impl<T, K> GcStore<T, K> {
    pub fn new() -> Self {
        Self { store: vec![], key_type: PhantomData }
    }

    pub fn insert(&mut self, obj: T) -> Handle<K> {
        self.store.push(obj);
        Handle(self.store.len() - 1, PhantomData)
    }

    pub fn lookup(&self, h: Handle<K>) -> &T {
        self.store.get(h.0).unwrap()
    }

    pub fn lookup_mut(&mut self, h: Handle<K>) -> &mut T {
        self.store.get_mut(h.0).unwrap()
    }

    pub fn inner(&self) -> &Vec<T> {
        &self.store
    }
}

