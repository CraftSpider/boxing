use criterion::Criterion;

#[allow(unused_mut)]
pub fn criterion() -> Criterion {
    let mut out = Criterion::default();
    #[cfg(unix)]
    {
        use pprof::criterion::{Output, PProfProfiler};
        out = out.with_profiler(PProfProfiler::new(1000, Output::Flamegraph(None)));
    }
    out.configure_from_args()
}
