//! Binary-size optimized mergesort inspired by https://github.com/voultapher/tiny-sort-rs.

use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::mem::MaybeUninit;
use crate::ptr;
use crate::slice::sort::stable::merge;

/// Tiny recursive top-down merge sort optimized for binary size. It has no adaptiveness whatsoever,
/// no run detection, etc.
#[inline(always)]
#[requires(scratch.len() >= (v.len() + 1) / 2)]
#[requires(v.len() <= usize::MAX)]
#[requires(size_of::<T>() > 0)]
#[requires(v.len() >= 2 ==> can_dereference(v.as_ptr()) && can_dereference(v.as_ptr().add(1)))]
#[requires(v.len() >= 2 ==> can_write(v.as_mut_ptr()) && can_write(v.as_mut_ptr().add(1)))]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
#[cfg_attr(kani, kani::modifies(scratch.as_mut_ptr()))]
pub fn mergesort<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    is_less: &mut F,
) {
    let len = v.len();

    if len > 2 {
        let mid = len / 2;

        // SAFETY: mid is in-bounds.
        unsafe {
            // Sort the left half recursively.
            mergesort(v.get_unchecked_mut(..mid), scratch, is_less);
            // Sort the right half recursively.
            mergesort(v.get_unchecked_mut(mid..), scratch, is_less);
        }

        merge::merge(v, scratch, mid, is_less);
    } else if len == 2 {
        // SAFETY: We checked the len, the pointers we create are valid and don't overlap.
        unsafe {
            let v_base = v.as_mut_ptr();
            let v_a = v_base;
            let v_b = v_base.add(1);

            if is_less(&*v_b, &*v_a) {
                ptr::swap_nonoverlapping(v_a, v_b, 1);
            }
        }
    }
}
#[cfg(kani)]
mod verify {
    use super::*;

    #[cfg(kani)]
    #[kani::proof_for_contract(mergesort)]
    fn proof_mergesort() {
        // Use a variable array size to test different scenarios
        let size = kani::any::<u8>() as usize % 10;

        // Create an array to sort
        let mut data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..size {
            data[i] = kani::any();
        }

        // Calculate required scratch size: (v.len() + 1) / 2
        let scratch_size = (size + 1) / 2;

        // Create a scratch space with sufficient size
        let mut scratch = [MaybeUninit::<i32>::uninit(); 10];

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        // This satisfies:
        // - scratch.len() >= (v.len() + 1) / 2
        // - v.len() <= usize::MAX (always true for our small array)
        // - size_of::<T>() > 0 (true for i32)
        // - v.len() >= 2 ==> can_dereference(v.as_ptr()) && can_dereference(v.as_ptr().add(1))
        // - v.len() >= 2 ==> can_write(v.as_mut_ptr()) && can_write(v.as_mut_ptr().add(1))
        mergesort(
            &mut data[..size],
            &mut scratch[..scratch_size],
            &mut is_less,
        );
    }
}
