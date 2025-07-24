use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::fmt;
use crate::iter::InPlaceIterable;
use crate::iter::adapters::SourceIter;
use crate::num::NonZero;
use crate::ops::{ControlFlow, Try};

/// An iterator that only accepts elements while `predicate` returns `Some(_)`.
///
/// This `struct` is created by the [`map_while`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`map_while`]: Iterator::map_while
/// [`Iterator`]: trait.Iterator.html
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "iter_map_while", since = "1.57.0")]
#[derive(Clone)]
pub struct MapWhile<I, P> {
    iter: I,
    predicate: P,
}

impl<I, P> MapWhile<I, P> {
    pub(in crate::iter) fn new(iter: I, predicate: P) -> MapWhile<I, P> {
        MapWhile { iter, predicate }
    }
}

#[stable(feature = "iter_map_while", since = "1.57.0")]
impl<I: fmt::Debug, P> fmt::Debug for MapWhile<I, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MapWhile").field("iter", &self.iter).finish()
    }
}

#[stable(feature = "iter_map_while", since = "1.57.0")]
impl<B, I: Iterator, P> Iterator for MapWhile<I, P>
where
    P: FnMut(I::Item) -> Option<B>,
{
    type Item = B;

    #[inline]
    fn next(&mut self) -> Option<B> {
        let x = self.iter.next()?;
        (self.predicate)(x)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper) // can't know a lower bound, due to the predicate
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, init: Acc, mut fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        let Self { iter, predicate } = self;
        iter.try_fold(init, |acc, x| match predicate(x) {
            Some(item) => ControlFlow::from_try(fold(acc, item)),
            None => ControlFlow::Break(try { acc }),
        })
        .into_try()
    }

    impl_fold_via_try_fold! { fold -> try_fold }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I, P> SourceIter for MapWhile<I, P>
where
    I: SourceIter,
{
    type Source = I::Source;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut I::Source {
        // SAFETY: unsafe function forwarding to unsafe function with the same requirements
        unsafe { SourceIter::as_inner(&mut self.iter) }
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I: InPlaceIterable, P> InPlaceIterable for MapWhile<I, P> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}
#[cfg(kani)]
mod verify {
    use super::*;

    #[cfg(kani)]
    #[kani::proof_for_contract(MapWhile::as_inner)]
    fn proof_for_mapwhile_as_inner() {
        use core::iter::SourceIter;

        // Create a simple iterator type that implements SourceIter
        struct SimpleIter {
            data: [u32; 5],
            index: usize,
        }

        impl Iterator for SimpleIter {
            type Item = u32;

            fn next(&mut self) -> Option<Self::Item> {
                if self.index < self.data.len() {
                    let item = self.data[self.index];
                    self.index += 1;
                    Some(item)
                } else {
                    None
                }
            }
        }

        // Implement SourceIter for SimpleIter
        unsafe impl SourceIter for SimpleIter {
            type Source = [u32; 5];

            unsafe fn as_inner(&mut self) -> &mut Self::Source {
                &mut self.data
            }
        }

        // Create a simple predicate function
        fn is_even(x: u32) -> Option<u64> {
            if x % 2 == 0 {
                Some((x as u64) * 2)
            } else {
                None
            }
        }

        // Create a SimpleIter instance
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: 0,
        };

        // Create a MapWhile with our SimpleIter and predicate
        let mut map_while = MapWhile {
            iter,
            predicate: is_even,
        };

        // Call the function
        unsafe {
            let _ = map_while.as_inner();
        }
    }
}
