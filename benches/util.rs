use criterion::Criterion;

pub fn criterion() -> Criterion {
    let mut out = Criterion::default();
    #[cfg(unix)]
    {
        use pprof::criterion::{PProfProfiler, Output};
        out = out.with_profiler(PProfProfiler::new(1000, Output::Flamegraph(None)));
    }
    out.configure_from_args()
}
