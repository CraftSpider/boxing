use std::hint::black_box;
use criterion::{Criterion, criterion_main, criterion_group, BenchmarkId};
use boxing::nan::raw::RawTag;
use boxing::nan::RawBox;

mod util;

fn new_float(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::from_f64");
    
    group
        .bench_function(
            BenchmarkId::from_parameter("0.0"),
            |b| b.iter(|| RawBox::from_f64(black_box(0.0))),
        )
        .bench_function(
            BenchmarkId::from_parameter("1.0"),
            |b| b.iter(|| RawBox::from_f64(black_box(1.0))),
        )
        .bench_function(
            BenchmarkId::from_parameter("inf"),
            |b| b.iter(|| RawBox::from_f64(black_box(f64::INFINITY))),
        )
        .bench_function(
            BenchmarkId::from_parameter("-inf"),
            |b| b.iter(|| RawBox::from_f64(black_box(f64::NEG_INFINITY))),
        )
        .bench_function(
            BenchmarkId::from_parameter("NaN"),
            |b| b.iter(|| RawBox::from_f64(black_box(f64::NAN))),
        );
}

fn new_data(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::from_data");
    
    let tagf1 = RawTag::new(false, 1);
    let tagt1 = RawTag::new(true, 1);
    let tagf7 = RawTag::new(false, 7);
    let tagt7 = RawTag::new(true, 7);
    
    group
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagf1), black_box([0; 6]))),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(true, 1), [0; 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagt1), black_box([0; 6]))),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 7), [0; 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagf7), black_box([0; 6]))),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(true, 7), [0; 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagt7), black_box([0; 6]))),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [255; 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagf1), black_box([255; 6]))),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [1, 2, 3, 4, 5, 6])"),
            |b| b.iter(|| RawBox::from_data(black_box(tagf1), black_box([1, 2, 3, 4, 5, 6]))),
        );
}

fn is_f64(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::is_f64");
    
    let f0 = RawBox::from_f64(0.0);
    let fnan = RawBox::from_f64(f64::NAN);
    let d0 = RawBox::from_data(RawTag::new(false, 1), [0; 6])
        .unwrap();
    let dfull = RawBox::from_data(RawTag::new(true, 7), [255; 6])
        .unwrap();
    
    group
        .bench_function(
            BenchmarkId::from_parameter("0.0"),
            |b| b.iter(|| black_box(&f0).is_float()),
        )
        .bench_function(
            BenchmarkId::from_parameter("nan"),
            |b| b.iter(|| black_box(&fnan).is_float()),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(&d0).is_f64()),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(&dfull).is_f64()),
        );
}

fn is_data(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::is_data");

    let f0 = RawBox::from_f64(0.0);
    let fnan = RawBox::from_f64(f64::NAN);
    let d0 = RawBox::from_data(RawTag::new(false, 1), [0; 6])
        .unwrap();
    let dfull = RawBox::from_data(RawTag::new(true, 7), [255; 6])
        .unwrap();

    group
        .bench_function(
            BenchmarkId::from_parameter("0.0"),
            |b| b.iter(|| black_box(&f0).is_value()),
        )
        .bench_function(
            BenchmarkId::from_parameter("nan"),
            |b| b.iter(|| black_box(&fnan).is_value()),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(&d0).is_data()),
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(&dfull).is_data()),
        );
}

fn into_f64(c: &mut Criterion) {
    let mut group = c.benchmark_group("RawBox::into_f64");
    
    let f0 = RawBox::from_f64(0.0);
    let fnan = RawBox::from_f64(f64::NAN);
    let tagf1 = RawBox::from_data(RawTag::new(false, 1), [0; 6])
        .unwrap();
    let tagt7 = RawBox::from_data(RawTag::new(true, 7), [255; 6])
        .unwrap();
    
    group
        .bench_function(
            BenchmarkId::from_parameter("0.0"),
            |b| b.iter(|| black_box(f0.clone()).into_float().unwrap())
        )
        .bench_function(
            BenchmarkId::from_parameter("nan"),
            |b| b.iter(|| black_box(fnan.clone()).into_float().unwrap())
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(false, 1), [0; 6])"),
            |b| b.iter(|| black_box(tagf1.clone()).into_f64().unwrap_err())
        )
        .bench_function(
            BenchmarkId::from_parameter("(RawTag(true, 7), [255; 6])"),
            |b| b.iter(|| black_box(tagt7.clone()).into_f64().unwrap_err())
        );
    
}

criterion_group!(
    name = float;
    config = util::criterion();
    targets = new_float, new_data, is_f64, is_data, into_f64
);

criterion_main!(float);
