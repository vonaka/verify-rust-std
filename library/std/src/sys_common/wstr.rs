//! This module contains constructs to work with 16-bit characters (UCS-2 or UTF-16)
#![feature(ub_checks)]
#![allow(dead_code)]

use core::ub_checks::Invariant;

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
use core::kani;
#[allow(unused_imports)]
#[unstable(feature = "ub_checks", issue = "none")]
use core::ub_checks::*;
use safety::{ensures, requires};

use crate::marker::PhantomData;
use crate::num::NonZero;
use crate::ptr::NonNull;

/// A safe iterator over a LPWSTR
/// (aka a pointer to a series of UTF-16 code units terminated by a NULL).
pub struct WStrUnits<'a> {
    // The pointer must never be null...
    lpwstr: NonNull<u16>,
    // ...and the memory it points to must be valid for this lifetime.
    lifetime: PhantomData<&'a [u16]>,
}

impl WStrUnits<'_> {
    /// Creates the iterator. Returns `None` if `lpwstr` is null.
    ///
    /// SAFETY: `lpwstr` must point to a null-terminated wide string that lives
    /// at least as long as the lifetime of this struct.
    #[requires(lpwstr as usize != 0)]
    pub unsafe fn new(lpwstr: *const u16) -> Option<Self> {
        Some(Self { lpwstr: NonNull::new(lpwstr as _)?, lifetime: PhantomData })
    }

    pub fn peek(&self) -> Option<NonZero<u16>> {
        // SAFETY: It's always safe to read the current item because we don't
        // ever move out of the array's bounds.
        unsafe { NonZero::new(*self.lpwstr.as_ptr()) }
    }

    /// Advance the iterator while `predicate` returns true.
    /// Returns the number of items it advanced by.
    pub fn advance_while<P: FnMut(NonZero<u16>) -> bool>(&mut self, mut predicate: P) -> usize {
        let mut counter = 0;
        while let Some(w) = self.peek() {
            if !predicate(w) {
                break;
            }
            counter += 1;
            self.next();
        }
        counter
    }
}

impl Iterator for WStrUnits<'_> {
    // This can never return zero as that marks the end of the string.
    type Item = NonZero<u16>;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: If NULL is reached we immediately return.
        // Therefore it's safe to advance the pointer after that.
        unsafe {
            let next = self.peek()?;
            self.lpwstr = NonNull::new_unchecked(self.lpwstr.as_ptr().add(1));
            Some(next)
        }
    }
}

#[unstable(feature = "ub_checks", issue = "none")]
impl<'a> Invariant for WStrUnits<'a> {
    fn is_safe(&self) -> bool {
        !self.lpwstr.as_ptr().is_null()
    }
}
