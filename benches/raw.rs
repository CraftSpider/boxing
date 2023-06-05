use boxing::nan::raw::{RawTag, Value};
use boxing::nan::RawBox;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;
use std::num::NonZeroU8;

mod util;

fn new_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::from_float");

    group
        .bench_function(BenchmarkId::from_parameter("0.0"), |b| {
            b.iter(|| RawBox::from_float(black_box(0.0)))
        })
        .bench_function(BenchmarkId::from_parameter("1.0"), |b| {
            b.iter(|| RawBox::from_float(black_box(1.0)))
        })
        .bench_function(BenchmarkId::from_parameter("inf"), |b| {
            b.iter(|| RawBox::from_float(black_box(f64::INFINITY)))
        })
        .bench_function(BenchmarkId::from_parameter("-inf"), |b| {
            b.iter(|| RawBox::from_float(black_box(f64::NEG_INFINITY)))
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| RawBox::from_float(black_box(f64::NAN)))
        });
}

fn new_value(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::from_value");

    let valf1 = Value::empty(RawTag::new(false, NonZeroU8::MIN));
    let valt1 = Value::empty(RawTag::new(true, NonZeroU8::MIN));
    let valf7 = Value::empty(RawTag::new(false, NonZeroU8::new(7).unwrap()));
    let valt7 = Value::empty(RawTag::new(true, NonZeroU8::new(7).unwrap()));

    let val_255 = Value::new(RawTag::new(false, NonZeroU8::MIN), [255; 6]);
    let val_123 = Value::new(RawTag::new(false, NonZeroU8::MIN), [1, 2, 3, 4, 5, 6]);

    group
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(valf1.clone()))),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(true, 1), [0; 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(valt1.clone()).clone())),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 7), [0; 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(valf7.clone()))),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(true, 7), [0; 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(valt7.clone()))),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [255; 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(val_255.clone()))),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [1, 2, 3, 4, 5, 6])"),
            |b| b.iter(|| RawBox::from_value(black_box(val_123.clone()))),
        );
}

fn is_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::is_float");

    let f0 = RawBox::from_float(0.0);
    let fnan = RawBox::from_float(f64::NAN);
    let d0 = RawBox::from_value(Value::new(RawTag::new(false, NonZeroU8::MIN), [0; 6]));
    let dfull = RawBox::from_value(Value::new(
        RawTag::new(true, NonZeroU8::new(7).unwrap()),
        [255; 6],
    ));

    group
        .bench_function(BenchmarkId::from_parameter("0.0"), |b| {
            b.iter(|| black_box(&f0).is_float())
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| black_box(&fnan).is_float())
        })
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(&d0).is_float()),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(&dfull).is_float()),
        );
}

fn is_data(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::is_value");

    let f0 = RawBox::from_float(0.0);
    let fnan = RawBox::from_float(f64::NAN);
    let d0 = RawBox::from_value(Value::new(RawTag::new(false, NonZeroU8::MIN), [0; 6]));
    let dfull = RawBox::from_value(Value::new(
        RawTag::new(true, NonZeroU8::new(7).unwrap()),
        [255; 6],
    ));

    group
        .bench_function(BenchmarkId::from_parameter("0.0"), |b| {
            b.iter(|| black_box(&f0).is_value())
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| black_box(&fnan).is_value())
        })
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(&d0).is_value()),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(&dfull).is_value()),
        );
}

fn into_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::into_float");

    let f0 = RawBox::from_float(0.0);
    let fnan = RawBox::from_float(f64::NAN);
    let valf1 = RawBox::from_value(Value::new(RawTag::new(false, NonZeroU8::MIN), [0; 6]));
    let valt7 = RawBox::from_value(Value::new(
        RawTag::new(true, NonZeroU8::new(7).unwrap()),
        [255; 6],
    ));

    group
        .bench_function(BenchmarkId::from_parameter("0.0"), |b| {
            b.iter(|| black_box(f0.clone()).into_float().unwrap())
        })
        .bench_function(BenchmarkId::from_parameter("nan"), |b| {
            b.iter(|| black_box(fnan.clone()).into_float().unwrap())
        })
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(valf1.clone()).into_float().unwrap_err()),
        )
        .bench_function(
            BenchmarkId::from_parameter("Value(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(valt7.clone()).into_float().unwrap_err()),
        );
}

criterion_group!(
    name = float;
    config = util::criterion();
    targets = new_float, new_value, is_float, is_data, into_float
);

criterion_main!(float);
