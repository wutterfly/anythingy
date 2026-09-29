use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::hint::black_box;

use anythingy::{Thing, ThingMap};
use criterion::{Criterion, criterion_group, criterion_main};

// Eight distinct types, so lookups are not trivially predictable.
#[allow(dead_code)]
struct A(u64);
#[allow(dead_code)]
struct B(u64);
#[allow(dead_code)]
struct C(u64);
#[allow(dead_code)]
struct D(u64);
#[allow(dead_code)]
struct E(u64);
#[allow(dead_code)]
struct F(u64);
#[allow(dead_code)]
struct G(u64);
#[allow(dead_code)]
struct H(u64);

/// The same pass-through hasher `ThingMap` uses, to compare hashers on their
/// own, separate from the unchecked reads.
#[derive(Default)]
struct PassThrough(u64);

impl Hasher for PassThrough {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write_u64(&mut self, value: u64) {
        self.0 = self.0.rotate_left(5) ^ value;
    }
    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }
}

macro_rules! fill {
    ($insert:expr) => {{
        $insert(A(1));
        $insert(B(2));
        $insert(C(3));
        $insert(D(4));
        $insert(E(5));
        $insert(F(6));
        $insert(G(7));
        $insert(H(8));
    }};
}

/// Reading one value by type out of a map holding eight.
fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_map_get");

    let mut thing_map = ThingMap::<24>::new();
    fill!(|v| {
        thing_map.insert(v);
    });
    group.bench_function("ThingMap", |b| {
        b.iter(|| black_box(&thing_map).get::<E>().unwrap().0);
    });

    let mut checked: HashMap<TypeId, Thing<24>, BuildHasherDefault<PassThrough>> =
        HashMap::default();
    checked.insert(TypeId::of::<A>(), Thing::new(A(1)));
    checked.insert(TypeId::of::<B>(), Thing::new(B(2)));
    checked.insert(TypeId::of::<C>(), Thing::new(C(3)));
    checked.insert(TypeId::of::<D>(), Thing::new(D(4)));
    checked.insert(TypeId::of::<E>(), Thing::new(E(5)));
    checked.insert(TypeId::of::<F>(), Thing::new(F(6)));
    checked.insert(TypeId::of::<G>(), Thing::new(G(7)));
    checked.insert(TypeId::of::<H>(), Thing::new(H(8)));
    group.bench_function("HashMap<TypeId, Thing> (checked get_ref)", |b| {
        b.iter(|| {
            black_box(&checked)
                .get(&TypeId::of::<E>())
                .unwrap()
                .get_ref::<E>()
                .0
        });
    });

    let mut boxed_sip: HashMap<TypeId, Box<dyn Any>> = HashMap::new();
    boxed_sip.insert(TypeId::of::<A>(), Box::new(A(1)));
    boxed_sip.insert(TypeId::of::<B>(), Box::new(B(2)));
    boxed_sip.insert(TypeId::of::<C>(), Box::new(C(3)));
    boxed_sip.insert(TypeId::of::<D>(), Box::new(D(4)));
    boxed_sip.insert(TypeId::of::<E>(), Box::new(E(5)));
    boxed_sip.insert(TypeId::of::<F>(), Box::new(F(6)));
    boxed_sip.insert(TypeId::of::<G>(), Box::new(G(7)));
    boxed_sip.insert(TypeId::of::<H>(), Box::new(H(8)));
    group.bench_function("HashMap<TypeId, Box<dyn Any>> (SipHash)", |b| {
        b.iter(|| {
            black_box(&boxed_sip)
                .get(&TypeId::of::<E>())
                .unwrap()
                .downcast_ref::<E>()
                .unwrap()
                .0
        });
    });

    let mut boxed_fast: HashMap<TypeId, Box<dyn Any>, BuildHasherDefault<PassThrough>> =
        HashMap::default();
    boxed_fast.insert(TypeId::of::<A>(), Box::new(A(1)));
    boxed_fast.insert(TypeId::of::<B>(), Box::new(B(2)));
    boxed_fast.insert(TypeId::of::<C>(), Box::new(C(3)));
    boxed_fast.insert(TypeId::of::<D>(), Box::new(D(4)));
    boxed_fast.insert(TypeId::of::<E>(), Box::new(E(5)));
    boxed_fast.insert(TypeId::of::<F>(), Box::new(F(6)));
    boxed_fast.insert(TypeId::of::<G>(), Box::new(G(7)));
    boxed_fast.insert(TypeId::of::<H>(), Box::new(H(8)));
    group.bench_function("HashMap<TypeId, Box<dyn Any>> (pass-through hasher)", |b| {
        b.iter(|| {
            black_box(&boxed_fast)
                .get(&TypeId::of::<E>())
                .unwrap()
                .downcast_ref::<E>()
                .unwrap()
                .0
        });
    });
    group.finish();
}

/// Modifying a value in place.
fn bench_get_mut(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_map_get_mut");

    let mut thing_map = ThingMap::<24>::new();
    fill!(|v| {
        thing_map.insert(v);
    });
    group.bench_function("ThingMap", |b| {
        b.iter(|| {
            let e = black_box(&mut thing_map).get_mut::<E>().unwrap();
            e.0 = e.0.wrapping_add(1);
        });
    });

    let mut boxed_sip: HashMap<TypeId, Box<dyn Any>> = HashMap::new();
    boxed_sip.insert(TypeId::of::<E>(), Box::new(E(5)));
    group.bench_function("HashMap<TypeId, Box<dyn Any>> (SipHash)", |b| {
        b.iter(|| {
            let e = black_box(&mut boxed_sip)
                .get_mut(&TypeId::of::<E>())
                .unwrap()
                .downcast_mut::<E>()
                .unwrap();
            e.0 = e.0.wrapping_add(1);
        });
    });
    group.finish();
}

/// Inserting and removing a value again, which exercises the allocation
/// behavior of small values (inline in `ThingMap`, boxed with `Box<dyn Any>`).
fn bench_insert_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_map_insert_remove");

    let mut thing_map = ThingMap::<24>::new();
    fill!(|v| {
        thing_map.insert(v);
    });
    group.bench_function("ThingMap", |b| {
        b.iter(|| {
            thing_map.insert(black_box(String::from("x")));
            thing_map.remove::<String>()
        });
    });

    let mut boxed_sip: HashMap<TypeId, Box<dyn Any>> = HashMap::new();
    group.bench_function("HashMap<TypeId, Box<dyn Any>> (SipHash)", |b| {
        b.iter(|| {
            boxed_sip.insert(
                TypeId::of::<String>(),
                Box::new(black_box(String::from("x"))),
            );
            boxed_sip.remove(&TypeId::of::<String>())
        });
    });
    group.finish();
}

criterion_group!(benches, bench_get, bench_get_mut, bench_insert_remove);
criterion_main!(benches);
