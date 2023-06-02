pub trait ArrayExt<const LEN: usize> {
    type Elem;

    fn truncate_to<const M: usize>(self) -> [Self::Elem; M];
}

impl<T: Default + Copy, const N: usize> ArrayExt<N> for [T; N] {
    type Elem = T;

    fn truncate_to<const M: usize>(self) -> [Self::Elem; M] {
        let copy_len = usize::min(N, M);
        let mut out = [T::default(); M];
        out[0..copy_len].copy_from_slice(&self[0..copy_len]);
        out
    }
}
