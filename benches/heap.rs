use boxing::nan::NanBox;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use std::hint::black_box;

mod util;

pub fn new_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("NanBox::from_float");

    group
        .bench_function(BenchmarkId::from_parameter("1.0"), |b| {
            b.iter(|| NanBox::<()>::from_float(black_box(1.0)))
        })
        .bench_function(BenchmarkId::from_parameter("0.0"), |b| {
            b.iter(|| NanBox::<()>::from_float(black_box(0.0)))
        })
        .bench_function(BenchmarkId::from_parameter("inf"), |b| {
            b.iter(|| NanBox::<()>::from_float(black_box(f64::INFINITY)))
        })
        .bench_function(BenchmarkId::from_parameter("-inf"), |b| {
            b.iter(|| NanBox::<()>::from_float(black_box(f64::NEG_INFINITY)))
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| NanBox::<()>::from_float(black_box(f64::NAN)))
        });
}

pub fn is_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("NanBox::is_float");

    let f0 = NanBox::<()>::from_float(0.0);
    let fnan = NanBox::<()>::from_float(f64::NAN);
    let u0 = NanBox::<()>::from_inline(0i32);
    let b0 = NanBox::<u128>::from_box(Box::new(0));

    group
        .bench_function(BenchmarkId::from_parameter("1.0"), |b| {
            b.iter(|| black_box(&f0).is_float())
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| black_box(&fnan).is_float())
        })
        .bench_function(BenchmarkId::from_parameter("0i32"), |b| {
            b.iter(|| black_box(&u0).is_float())
        })
        .bench_function(BenchmarkId::from_parameter("0u128"), |b| {
            b.iter(|| black_box(&b0).is_float())
        });
}

pub fn new_inline(c: &mut Criterion) {
    let mut group = c.benchmark_group("NanBox::from_inline");

    let num = 1u128;

    group
        .bench_function(BenchmarkId::from_parameter("true"), |b| {
            b.iter(|| NanBox::<()>::from_inline(black_box(true)))
        })
        .bench_function(BenchmarkId::from_parameter("false"), |b| {
            b.iter(|| NanBox::<()>::from_inline(black_box(false)))
        })
        .bench_function(BenchmarkId::from_parameter("u32::MAX"), |b| {
            b.iter(|| NanBox::<()>::from_inline(black_box(u32::MAX)))
        })
        .bench_function(BenchmarkId::from_parameter("i32::MAX"), |b| {
            b.iter(|| NanBox::<()>::from_inline(black_box(i32::MAX)))
        })
        .bench_function(BenchmarkId::from_parameter("&u128"), |b| {
            b.iter(|| NanBox::<u128>::from_inline(black_box(&num)))
        });
}

pub fn new_boxed(c: &mut Criterion) {
    let mut group = c.benchmark_group("NanBox::from_boxed");

    group
        .bench_function(BenchmarkId::from_parameter("1i128"), |b| {
            b.iter_batched(
                || Box::new(1i128),
                |data| NanBox::from_box(black_box(data)),
                BatchSize::SmallInput,
            )
        })
        .bench_function(BenchmarkId::from_parameter("-1i32"), |b| {
            b.iter_batched(
                || Box::new(-1i128),
                |data| NanBox::from_box(black_box(data)),
                BatchSize::SmallInput,
            )
        });
}

criterion_group!(
    name = float;
    config = util::criterion();
    targets = new_float, is_float,
);

criterion_group!(
    name = inline;
    config = util::criterion();
    targets = new_inline,
);

criterion_group!(
    name = boxed;
    config = util::criterion();
    targets = new_boxed,
);

criterion_main!(float, inline, boxed);
