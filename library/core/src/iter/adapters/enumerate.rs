use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused, TrustedLen};
use crate::num::NonZero;
use crate::ops::Try;

/// An iterator that yields the current count and the element during iteration.
///
/// This `struct` is created by the [`enumerate`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`enumerate`]: Iterator::enumerate
/// [`Iterator`]: trait.Iterator.html
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_diagnostic_item = "Enumerate"]
pub struct Enumerate<I> {
    iter: I,
    count: usize,
}
impl<I> Enumerate<I> {
    pub(in crate::iter) fn new(iter: I) -> Enumerate<I> {
        Enumerate { iter, count: 0 }
    }

    /// Retrieve the current position of the iterator.
    ///
    /// If the iterator has not advanced, the position returned will be 0.
    ///
    /// The position may also exceed the bounds of the iterator to allow for calculating
    /// the displacement of the iterator from following calls to [`Iterator::next`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(next_index)]
    ///
    /// let arr = ['a', 'b'];
    ///
    /// let mut iter = arr.iter().enumerate();
    ///
    /// assert_eq!(iter.next_index(), 0);
    /// assert_eq!(iter.next(), Some((0, &'a')));
    ///
    /// assert_eq!(iter.next_index(), 1);
    /// assert_eq!(iter.next_index(), 1);
    /// assert_eq!(iter.next(), Some((1, &'b')));
    ///
    /// assert_eq!(iter.next_index(), 2);
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next_index(), 2);
    /// ```
    #[inline]
    #[unstable(feature = "next_index", issue = "130711")]
    pub fn next_index(&self) -> usize {
        self.count
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    type Item = (usize, <I as Iterator>::Item);

    /// # Overflow Behavior
    ///
    /// The method does no guarding against overflows, so enumerating more than
    /// `usize::MAX` elements either produces the wrong result or panics. If
    /// overflow checks are enabled, a panic is guaranteed.
    ///
    /// # Panics
    ///
    /// Might panic if the index of the element overflows a `usize`.
    #[inline]
    #[rustc_inherit_overflow_checks]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.next()?;
        let i = self.count;
        self.count += 1;
        Some((i, a))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    #[rustc_inherit_overflow_checks]
    fn nth(&mut self, n: usize) -> Option<(usize, I::Item)> {
        let a = self.iter.nth(n)?;
        let i = self.count + n;
        self.count = i + 1;
        Some((i, a))
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        #[inline]
        fn enumerate<'a, T, Acc, R>(
            count: &'a mut usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> R + 'a,
        ) -> impl FnMut(Acc, T) -> R + 'a {
            #[rustc_inherit_overflow_checks]
            move |acc, item| {
                let acc = fold(acc, (*count, item));
                *count += 1;
                acc
            }
        }

        self.iter.try_fold(init, enumerate(&mut self.count, fold))
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        #[inline]
        fn enumerate<T, Acc>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> Acc,
        ) -> impl FnMut(Acc, T) -> Acc {
            #[rustc_inherit_overflow_checks]
            move |acc, item| {
                let acc = fold(acc, (count, item));
                count += 1;
                acc
            }
        }

        self.iter.fold(init, enumerate(self.count, fold))
    }

    #[inline]
    #[rustc_inherit_overflow_checks]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let remaining = self.iter.advance_by(n);
        let advanced = match remaining {
            Ok(()) => n,
            Err(rem) => n - rem.get(),
        };
        self.count += advanced;
        remaining
    }

    #[rustc_inherit_overflow_checks]
    #[inline]
    #[requires(can_dereference(&mut self.iter as *mut _))]
    #[requires(can_dereference(&self.iter as *const _ as *const u8))]
    #[requires(can_dereference(self as *const _ as *const u8))]
    #[requires(idx < self.len())]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> <Self as Iterator>::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        let value = unsafe { try_get_unchecked(&mut self.iter, idx) };
        (self.count + idx, value)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> DoubleEndedIterator for Enumerate<I>
where
    I: ExactSizeIterator + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.next_back()?;
        let len = self.iter.len();
        // Can safely add, `ExactSizeIterator` promises that the number of
        // elements fits into a `usize`.
        Some((self.count + len, a))
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.nth_back(n)?;
        let len = self.iter.len();
        // Can safely add, `ExactSizeIterator` promises that the number of
        // elements fits into a `usize`.
        Some((self.count + len, a))
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        // Can safely add and subtract the count, as `ExactSizeIterator` promises
        // that the number of elements fits into a `usize`.
        fn enumerate<T, Acc, R>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> R,
        ) -> impl FnMut(Acc, T) -> R {
            move |acc, item| {
                count -= 1;
                fold(acc, (count, item))
            }
        }

        let count = self.count + self.iter.len();
        self.iter.try_rfold(init, enumerate(count, fold))
    }

    #[inline]
    fn rfold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        // Can safely add and subtract the count, as `ExactSizeIterator` promises
        // that the number of elements fits into a `usize`.
        fn enumerate<T, Acc>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> Acc,
        ) -> impl FnMut(Acc, T) -> Acc {
            move |acc, item| {
                count -= 1;
                fold(acc, (count, item))
            }
        }

        let count = self.count + self.iter.len();
        self.iter.rfold(init, enumerate(count, fold))
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        // we do not need to update the count since that only tallies the number of items
        // consumed from the front. consuming items from the back can never reduce that.
        self.iter.advance_back_by(n)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> ExactSizeIterator for Enumerate<I>
where
    I: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.iter.len()
    }

    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccess for Enumerate<I> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccessNoCoerce for Enumerate<I>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = I::MAY_HAVE_SIDE_EFFECT;
}

#[stable(feature = "fused", since = "1.26.0")]
impl<I> FusedIterator for Enumerate<I> where I: FusedIterator {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused> TrustedFused for Enumerate<I> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<I> TrustedLen for Enumerate<I> where I: TrustedLen {}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I> SourceIter for Enumerate<I>
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
unsafe impl<I: InPlaceIterable> InPlaceIterable for Enumerate<I> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<I: Default> Default for Enumerate<I> {
    /// Creates an `Enumerate` iterator from the default value of `I`
    /// ```
    /// # use core::slice;
    /// # use std::iter::Enumerate;
    /// let iter: Enumerate<slice::Iter<'_, u8>> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Enumerate::new(Default::default())
    }
}
#[cfg(kani)]
mod verify {
    use super::*;
    #[cfg(kani)]
    #[kani::proof_for_contract(Enumerate::__iterator_get_unchecked)]
    fn proof_for_enumerate_iterator_get_unchecked() {
        use core::iter::{ExactSizeIterator, TrustedRandomAccessNoCoerce};

        // Create a simple iterator that implements TrustedRandomAccessNoCoerce
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

        // Create a SimpleIter instance with potentially consumed elements
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: kani::any::<usize>() % 6, // 0 to 5 (including empty case)
        };

        // Create an Enumerate with our SimpleIter
        let mut enumerate = Enumerate {
            iter,
            count: kani::any::<usize>() % 10, // Some arbitrary count
        };

        // Choose an index and ensure it's within bounds
        let idx = if enumerate.len() > 0 {
            kani::any::<usize>() % enumerate.len()
        } else {
            0
        };

        // Call the function only if we have elements
        if enumerate.len() > 0 {
            unsafe {
                let _ = enumerate.__iterator_get_unchecked(idx);
            }
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(Enumerate::as_inner)]
    fn proof_for_enumerate_as_inner() {
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

        // Create a SimpleIter instance with potentially consumed elements
        let mut iter = SimpleIter {
            data: [1, 2, 3, 4, 5],
            index: kani::any::<usize>() % 6, // 0 to 5 (including empty case)
        };

        // Create an Enumerate with our SimpleIter
        let mut enumerate = Enumerate {
            iter,
            count: kani::any::<usize>() % 10, // Some arbitrary count
        };

        // Call the function
        unsafe {
            let _ = enumerate.as_inner();
        }
    }
}
