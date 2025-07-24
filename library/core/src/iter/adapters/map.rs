use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::fmt;
use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused, TrustedLen, UncheckedIterator};
use crate::num::NonZero;
use crate::ops::Try;

/// An iterator that maps the values of `iter` with `f`.
///
/// This `struct` is created by the [`map`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`map`]: Iterator::map
/// [`Iterator`]: trait.Iterator.html
///
/// # Notes about side effects
///
/// The [`map`] iterator implements [`DoubleEndedIterator`], meaning that
/// you can also [`map`] backwards:
///
/// ```rust
/// let v: Vec<i32> = [1, 2, 3].into_iter().map(|x| x + 1).rev().collect();
///
/// assert_eq!(v, [4, 3, 2]);
/// ```
///
/// [`DoubleEndedIterator`]: trait.DoubleEndedIterator.html
///
/// But if your closure has state, iterating backwards may act in a way you do
/// not expect. Let's go through an example. First, in the forward direction:
///
/// ```rust
/// let mut c = 0;
///
/// for pair in ['a', 'b', 'c'].into_iter()
///                                .map(|letter| { c += 1; (letter, c) }) {
///     println!("{pair:?}");
/// }
/// ```
///
/// This will print `('a', 1), ('b', 2), ('c', 3)`.
///
/// Now consider this twist where we add a call to `rev`. This version will
/// print `('c', 1), ('b', 2), ('a', 3)`. Note that the letters are reversed,
/// but the values of the counter still go in order. This is because `map()` is
/// still being called lazily on each item, but we are popping items off the
/// back of the vector now, instead of shifting them from the front.
///
/// ```rust
/// let mut c = 0;
///
/// for pair in ['a', 'b', 'c'].into_iter()
///                                .map(|letter| { c += 1; (letter, c) })
///                                .rev() {
///     println!("{pair:?}");
/// }
/// ```
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct Map<I, F> {
    // Used for `SplitWhitespace` and `SplitAsciiWhitespace` `as_str` methods
    pub(crate) iter: I,
    f: F,
}

impl<I, F> Map<I, F> {
    pub(in crate::iter) fn new(iter: I, f: F) -> Map<I, F> {
        Map { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<I: fmt::Debug, F> fmt::Debug for Map<I, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Map").field("iter", &self.iter).finish()
    }
}

fn map_fold<T, B, Acc>(
    mut f: impl FnMut(T) -> B,
    mut g: impl FnMut(Acc, B) -> Acc,
) -> impl FnMut(Acc, T) -> Acc {
    move |acc, elt| g(acc, f(elt))
}

fn map_try_fold<'a, T, B, Acc, R>(
    f: &'a mut impl FnMut(T) -> B,
    mut g: impl FnMut(Acc, B) -> R + 'a,
) -> impl FnMut(Acc, T) -> R + 'a {
    move |acc, elt| g(acc, f(elt))
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: Iterator, F> Iterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    type Item = B;

    #[inline]
    fn next(&mut self) -> Option<B> {
        self.iter.next().map(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn try_fold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
    where
        Self: Sized,
        G: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_fold(init, map_try_fold(&mut self.f, g))
    }

    fn fold<Acc, G>(self, init: Acc, g: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.fold(init, map_fold(self.f, g))
    }

    #[inline]
    #[requires(can_dereference(&mut self.iter as *mut _))]
    #[requires(idx < self.len())]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> B
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        unsafe { (self.f)(try_get_unchecked(&mut self.iter, idx)) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: DoubleEndedIterator, F> DoubleEndedIterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    #[inline]
    fn next_back(&mut self) -> Option<B> {
        self.iter.next_back().map(&mut self.f)
    }

    fn try_rfold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
    where
        Self: Sized,
        G: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_rfold(init, map_try_fold(&mut self.f, g))
    }

    fn rfold<Acc, G>(self, init: Acc, g: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.rfold(init, map_fold(self.f, g))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: ExactSizeIterator, F> ExactSizeIterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    fn len(&self) -> usize {
        self.iter.len()
    }

    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<B, I: FusedIterator, F> FusedIterator for Map<I, F> where F: FnMut(I::Item) -> B {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused, F> TrustedFused for Map<I, F> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<B, I, F> TrustedLen for Map<I, F>
where
    I: TrustedLen,
    F: FnMut(I::Item) -> B,
{
}

impl<B, I, F> UncheckedIterator for Map<I, F>
where
    I: UncheckedIterator,
    F: FnMut(I::Item) -> B,
{
    #[requires(can_dereference(&mut self.iter as *mut _))]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn next_unchecked(&mut self) -> B {
        // SAFETY: `Map` is 1:1 with the inner iterator, so if the caller promised
        // that there's an element left, the inner iterator has one too.
        let item = unsafe { self.iter.next_unchecked() };
        (self.f)(item)
    }
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I, F> TrustedRandomAccess for Map<I, F> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I, F> TrustedRandomAccessNoCoerce for Map<I, F>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = true;
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I, F> SourceIter for Map<I, F>
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
unsafe impl<I: InPlaceIterable, F> InPlaceIterable for Map<I, F> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}
#[cfg(kani)]
mod verify {
    use super::*;
    #[cfg(kani)]
    #[kani::proof_for_contract(Map::__iterator_get_unchecked)]
    fn proof_for_map_iterator_get_unchecked() {
        use core::iter::{ExactSizeIterator, TrustedRandomAccessNoCoerce};

        // Create a simple iterator that implements TrustedRandomAccessNoCoerce
        struct SimpleIter {
            data: [u32; 5],
            index: usize,
        }

        impl SimpleIter {
            fn has_elements(&self) -> bool {
                self.index < self.data.len()
            }
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

            fn size_hint(&self) -> (usize, Option<usize>) {
                let remaining = self.data.len() - self.index;
                (remaining, Some(remaining))
            }
        }

        impl ExactSizeIterator for SimpleIter {
            fn len(&self) -> usize {
                self.data.len() - self.index
            }
        }

        // Implement TrustedRandomAccessNoCoerce for SimpleIter
        unsafe impl TrustedRandomAccessNoCoerce for SimpleIter {
            const MAY_HAVE_SIDE_EFFECT: bool = false;

            unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
                self.data[self.index + idx]
            }
        }

        // Create a simple mapping function
        fn double(x: u32) -> u64 {
            (x as u64) * 2
        }

        // Create a SimpleIter instance
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: 0,
        };

        // Create a Map with our SimpleIter and mapping function
        let mut map = Map { iter, f: double };

        // Choose an index and ensure it's within bounds
        let idx = if map.len() > 0 {
            kani::any::<usize>() % map.len()
        } else {
            0
        };

        // Call the function only if we have elements
        if map.len() > 0 {
            unsafe {
                let _ = map.__iterator_get_unchecked(idx);
            }
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(Map::next_unchecked)]
    fn proof_for_map_next_unchecked() {
        use core::iter::UncheckedIterator;

        // Create a simple iterator that implements UncheckedIterator
        struct SimpleIter {
            data: [u32; 5],
            index: usize,
        }

        impl SimpleIter {
            fn has_elements(&self) -> bool {
                self.index < self.data.len()
            }
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

            fn size_hint(&self) -> (usize, Option<usize>) {
                let remaining = self.data.len() - self.index;
                (remaining, Some(remaining))
            }
        }

        impl ExactSizeIterator for SimpleIter {
            fn len(&self) -> usize {
                self.data.len() - self.index
            }

            fn is_empty(&self) -> bool {
                self.index >= self.data.len()
            }
        }

        // Implement UncheckedIterator for SimpleIter
        impl UncheckedIterator for SimpleIter {
            unsafe fn next_unchecked(&mut self) -> Self::Item {
                let item = self.data[self.index];
                self.index += 1;
                item
            }
        }

        // Create a simple mapping function
        fn double(x: u32) -> u64 {
            (x as u64) * 2
        }

        // Create a SimpleIter instance with potentially consumed elements
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: kani::any::<usize>() % 5, // 0 to 4 (ensuring at least one element)
        };

        // Create a Map with our SimpleIter and mapping function
        let mut map = Map { iter, f: double };

        // Call the function only if we have elements
        if !map.is_empty() {
            unsafe {
                let _ = map.next_unchecked();
            }
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(Map::as_inner)]
    fn proof_for_map_as_inner() {
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

        // Create a simple mapping function
        fn double(x: u32) -> u64 {
            (x as u64) * 2
        }

        // Create a SimpleIter instance
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: 0,
        };

        // Create a Map with our SimpleIter and mapping function
        let mut map = Map { iter, f: double };

        // Call the function
        unsafe {
            let _ = map.as_inner();
        }
    }
}
