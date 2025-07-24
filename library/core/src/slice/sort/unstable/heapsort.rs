//! This module contains a branchless heapsort as fallback for unstable quicksort.

use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::{cmp, intrinsics, ptr};

/// Sorts `v` using heapsort, which guarantees *O*(*n* \* log(*n*)) worst-case.
///
/// Never inline this, it sits the main hot-loop in `recurse` and is meant as unlikely algorithmic
/// fallback.
#[inline(never)]
#[requires(v.len() <= usize::MAX / 2)]
#[requires(v.len() > 0 ==> can_write(v.as_mut_ptr()))]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
pub(crate) fn heapsort<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();

    for i in (0..len + len / 2).rev() {
        let sift_idx = if i >= len {
            i - len
        } else {
            v.swap(0, i);
            0
        };

        // SAFETY: The above calculation ensures that `sift_idx` is either 0 or
        // `(len..(len + (len / 2))) - len`, which simplifies to `0..(len / 2)`.
        // This guarantees the required `sift_idx <= len`.
        unsafe {
            sift_down(&mut v[..cmp::min(i, len)], sift_idx, is_less);
        }
    }
}

// This binary heap respects the invariant `parent >= child`.
//
// SAFETY: The caller has to guarantee that `node <= v.len()`.
#[inline(always)]
#[requires(node <= v.len())]
#[requires(2 * node + 1 < usize::MAX)]
#[requires(node != 2 * node + 1 && node != 2 * node + 2)]
#[requires(can_dereference(v.as_ptr().add(node)))]
#[requires(node < v.len() ==> can_dereference(v.as_ptr().add(2 * node + 1)))]
#[requires(2 * node + 2 <= v.len() ==> can_dereference(v.as_ptr().add(2 * node + 2)))]
#[requires(can_dereference(v.as_ptr().add(i)) for i in 0..v.len())]
#[requires(v.len() < isize::MAX as usize)]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
unsafe fn sift_down<T, F>(v: &mut [T], mut node: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: See function safety.
    unsafe {
        intrinsics::assume(node <= v.len());
    }

    let len = v.len();

    let v_base = v.as_mut_ptr();

    loop {
        // Children of `node`.
        let mut child = 2 * node + 1;
        if child >= len {
            break;
        }

        // SAFETY: The invariants and checks guarantee that both node and child are in-bounds.
        unsafe {
            // Choose the greater child.
            if child + 1 < len {
                // We need a branch to be sure not to out-of-bounds index,
                // but it's highly predictable.  The comparison, however,
                // is better done branchless, especially for primitives.
                child += is_less(&*v_base.add(child), &*v_base.add(child + 1)) as usize;
            }

            // Stop if the invariant holds at `node`.
            if !is_less(&*v_base.add(node), &*v_base.add(child)) {
                break;
            }

            ptr::swap_nonoverlapping(v_base.add(node), v_base.add(child), 1);
        }

        node = child;
    }
}
#[cfg(kani)]
mod verify {
    use super::*;
    #[cfg(kani)]
    #[kani::proof_for_contract(heapsort)]
    fn proof_heapsort() {
        // Use a variable array size to test different scenarios
        // Include the possibility of an empty array
        let size = kani::any::<u8>() as usize % 20;

        // Create an array to sort
        let mut data = [0i32; 20];

        // Initialize with arbitrary values
        for i in 0..size {
            data[i] = kani::any();
        }

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        heapsort(&mut data[..size], &mut is_less);
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(sift_down)]
    fn proof_sift_down() {
        // Use a variable array size to test different scenarios
        let size = 1 + (kani::any::<u8>() as usize % 19);

        // Create an array to work with
        let mut data = [0i32; 20];

        // Initialize with arbitrary values
        for i in 0..size {
            data[i] = kani::any();
        }

        // Choose a node index that satisfies our preconditions
        // We need:
        // - node <= v.len()
        // - 2 * node + 1 < usize::MAX (always true for small arrays)
        // - node != 2 * node + 1 && node != 2 * node + 2
        let node = if size <= 2 {
            // For very small arrays, use 0 as it's always valid
            0
        } else if kani::any() {
            // Test the root node
            0
        } else {
            // Test internal nodes, but ensure node < size/2 to avoid
            // the case where node == 2*node+1 or node == 2*node+2
            kani::any::<u8>() as usize % (size / 2)
        };

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        unsafe {
            sift_down(&mut data[..size], node, &mut is_less);
        }
    }
}
