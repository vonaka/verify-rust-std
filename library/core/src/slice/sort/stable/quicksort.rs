//! This module contains a stable quicksort and partition implementation.

use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::mem::{ManuallyDrop, MaybeUninit};
use crate::slice::sort::shared::FreezeMarker;
use crate::slice::sort::shared::pivot::choose_pivot;
use crate::slice::sort::shared::smallsort::StableSmallSortTypeImpl;
use crate::{intrinsics, ptr};

/// Sorts `v` recursively using quicksort.
/// `scratch.len()` must be at least `max(v.len() - v.len() / 2, SMALL_SORT_GENERAL_SCRATCH_LEN)`
/// otherwise the implementation may abort.
///
/// `limit` when initialized with `c*log(v.len())` for some c ensures we do not
/// overflow the stack or go quadratic.
#[inline(never)]
#[requires(scratch.len() >= max(v.len() - v.len() / 2, SMALL_SORT_GENERAL_SCRATCH_LEN))]
#[requires(v.len() <= isize::MAX as usize)]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
#[cfg_attr(kani, kani::modifies(scratch.as_mut_ptr()))]
pub fn quicksort<T, F: FnMut(&T, &T) -> bool>(
    mut v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    mut limit: u32,
    mut left_ancestor_pivot: Option<&T>,
    is_less: &mut F,
) {
    loop {
        let len = v.len();

        if len <= T::small_sort_threshold() {
            T::small_sort(v, scratch, is_less);
            return;
        }

        if limit == 0 {
            // We have had too many bad pivots, switch to O(n log n) fallback
            // algorithm. In our case that is driftsort in eager mode.
            crate::slice::sort::stable::drift::sort(v, scratch, true, is_less);
            return;
        }
        limit -= 1;

        let pivot_pos = choose_pivot(v, is_less);
        // SAFETY: choose_pivot promises to return a valid pivot index.
        unsafe {
            intrinsics::assume(pivot_pos < v.len());
        }

        // SAFETY: We only access the temporary copy for Freeze types, otherwise
        // self-modifications via `is_less` would not be observed and this would
        // be unsound. Our temporary copy does not escape this scope.
        let pivot_copy = unsafe { ManuallyDrop::new(ptr::read(&v[pivot_pos])) };
        let pivot_ref = (!has_direct_interior_mutability::<T>()).then_some(&*pivot_copy);

        // We choose a pivot, and check if this pivot is equal to our left
        // ancestor. If true, we do a partition putting equal elements on the
        // left and do not recurse on it. This gives O(n log k) sorting for k
        // distinct values, a strategy borrowed from pdqsort. For types with
        // interior mutability we can't soundly create a temporary copy of the
        // ancestor pivot, and use left_partition_len == 0 as our method for
        // detecting when we re-use a pivot, which means we do at most three
        // partition operations with pivot p instead of the optimal two.
        let mut perform_equal_partition = false;
        if let Some(la_pivot) = left_ancestor_pivot {
            perform_equal_partition = !is_less(la_pivot, &v[pivot_pos]);
        }

        let mut left_partition_len = 0;
        if !perform_equal_partition {
            left_partition_len = stable_partition(v, scratch, pivot_pos, false, is_less);
            perform_equal_partition = left_partition_len == 0;
        }

        if perform_equal_partition {
            let mid_eq = stable_partition(v, scratch, pivot_pos, true, &mut |a, b| !is_less(b, a));
            v = &mut v[mid_eq..];
            left_ancestor_pivot = None;
            continue;
        }

        // Process left side with the next loop iter, right side with recursion.
        let (left, right) = v.split_at_mut(left_partition_len);
        quicksort(right, scratch, limit, pivot_ref, is_less);
        v = left;
    }
}

/// Partitions `v` using pivot `p = v[pivot_pos]` and returns the number of
/// elements less than `p`. The relative order of elements that compare < p and
/// those that compare >= p is preserved - it is a stable partition.
///
/// If `is_less` is not a strict total order or panics, `scratch.len() < v.len()`,
/// or `pivot_pos >= v.len()`, the result and `v`'s state is sound but unspecified.
#[requires(scratch.len() >= v.len())]
#[requires(pivot_pos < v.len())]
#[requires(can_dereference(v.as_ptr().add(i)) for i in 0..v.len())]
#[requires(can_dereference(v.as_ptr().add(pivot_pos)))]
#[requires(can_write(MaybeUninit::slice_as_mut_ptr(scratch).add(i)) for i in 0..v.len())]
#[requires(!same_allocation(v.as_ptr(), MaybeUninit::slice_as_mut_ptr(scratch)))]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
#[cfg_attr(kani, kani::modifies(scratch.as_mut_ptr()))]
fn stable_partition<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    pivot_pos: usize,
    pivot_goes_left: bool,
    is_less: &mut F,
) -> usize {
    let len = v.len();

    if intrinsics::unlikely(scratch.len() < len || pivot_pos >= len) {
        core::intrinsics::abort()
    }

    let v_base = v.as_ptr();
    let scratch_base = MaybeUninit::slice_as_mut_ptr(scratch);

    // The core idea is to write the values that compare as less-than to the left
    // side of `scratch`, while the values that compared as greater or equal than
    // `v[pivot_pos]` go to the right side of `scratch` in reverse. See
    // PartitionState for details.

    // SAFETY: see individual comments.
    unsafe {
        // SAFETY: we made sure the scratch has length >= len and that pivot_pos
        // is in-bounds. v and scratch are disjoint slices.
        let pivot = v_base.add(pivot_pos);
        let mut state = PartitionState::new(v_base, scratch_base, len);

        let mut pivot_in_scratch = ptr::null_mut();
        let mut loop_end_pos = pivot_pos;

        // SAFETY: this loop is equivalent to calling state.partition_one
        // exactly len times.
        loop {
            // Ideally the outer loop won't be unrolled, to save binary size,
            // but we do want the inner loop to be unrolled for small types, as
            // this gave significant performance boosts in benchmarks. Unrolling
            // through for _ in 0..UNROLL_LEN { .. } instead of manually improves
            // compile times but has a ~10-20% performance penalty on opt-level=s.
            if const { size_of::<T>() <= 16 } {
                const UNROLL_LEN: usize = 4;
                let unroll_end = v_base.add(loop_end_pos.saturating_sub(UNROLL_LEN - 1));
                while state.scan < unroll_end {
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                    state.partition_one(is_less(&*state.scan, &*pivot));
                }
            }

            let loop_end = v_base.add(loop_end_pos);
            while state.scan < loop_end {
                state.partition_one(is_less(&*state.scan, &*pivot));
            }

            if loop_end_pos == len {
                break;
            }

            // We avoid comparing pivot with itself, as this could create deadlocks for
            // certain comparison operators. We also store its location later for later.
            pivot_in_scratch = state.partition_one(pivot_goes_left);

            loop_end_pos = len;
        }

        // `pivot` must be copied into its correct position again, because a
        // comparison operator might have modified it.
        if has_direct_interior_mutability::<T>() {
            ptr::copy_nonoverlapping(pivot, pivot_in_scratch, 1);
        }

        // SAFETY: partition_one being called exactly len times guarantees that scratch
        // is initialized with a permuted copy of `v`, and that num_left <= v.len().
        // Copying scratch[0..num_left] and scratch[num_left..v.len()] back is thus
        // sound, as the values in scratch will never be read again, meaning our copies
        // semantically act as moves, permuting `v`.

        // Copy all the elements < p directly from swap to v.
        let v_base = v.as_mut_ptr();
        ptr::copy_nonoverlapping(scratch_base, v_base, state.num_left);

        // Copy the elements >= p in reverse order.
        for i in 0..len - state.num_left {
            ptr::copy_nonoverlapping(
                scratch_base.add(len - 1 - i),
                v_base.add(state.num_left + i),
                1,
            );
        }

        state.num_left
    }
}

struct PartitionState<T> {
    // The start of the scratch auxiliary memory.
    scratch_base: *mut T,
    // The current element that is being looked at, scans left to right through slice.
    scan: *const T,
    // Counts the number of elements that went to the left side, also works around:
    // https://github.com/rust-lang/rust/issues/117128
    num_left: usize,
    // Reverse scratch output pointer.
    scratch_rev: *mut T,
}

impl<T> PartitionState<T> {
    /// # Safety
    ///
    /// `scan` and `scratch` must point to valid disjoint buffers of length `len`. The
    /// scan buffer must be initialized.
    #[requires(scan.add(len) <= scratch.add(len))]
    #[requires(!same_allocation(scan, scratch) || scan.add(len) <= scratch || scan >= scratch.add(len))]
    #[requires(can_dereference(scan.add(i)) for i in 0..len)]
    #[requires(can_write(scratch.add(i)) for i in 0..len)]
    #[requires(len > 0)]
    unsafe fn new(scan: *const T, scratch: *mut T, len: usize) -> Self {
        // SAFETY: See function safety comment.
        unsafe { Self { scratch_base: scratch, scan, num_left: 0, scratch_rev: scratch.add(len) } }
    }

    /// Depending on the value of `towards_left` this function will write a value
    /// to the growing left or right side of the scratch memory. This forms the
    /// branchless core of the partition.
    ///
    /// # Safety
    ///
    /// This function may be called at most `len` times. If it is called exactly
    /// `len` times the scratch buffer then contains a copy of each element from
    /// the scan buffer exactly once - a permutation, and num_left <= len.
    #[requires(self.scan < self.scratch_rev)]
    #[requires(can_dereference(self.scan))]
    #[requires(can_write(self.scratch_base.add(self.num_left)) || can_write(self.scratch_rev))]
    #[requires(self.num_left < self.scratch_rev.offset_from(self.scratch_base) as usize)]
    #[requires(self.scratch_base.add(self.num_left) < self.scratch_rev)]
    #[requires(can_write(self.scratch_rev.sub(1)))]
    #[cfg_attr(kani, kani::modifies(self.scratch_base.add(self.num_left)))]
    #[cfg_attr(kani, kani::modifies(self.scratch_rev))]
    unsafe fn partition_one(&mut self, towards_left: bool) -> *mut T {
        // SAFETY: see individual comments.
        unsafe {
            // SAFETY: in-bounds because this function is called at most len times, and thus
            // right now is incremented at most len - 1 times. Similarly, num_left < len and
            // num_right < len, where num_right == i - num_left at the start of the ith
            // iteration (zero-indexed).
            self.scratch_rev = self.scratch_rev.sub(1);

            // SAFETY: now we have scratch_rev == base + len - (i + 1). This means
            // scratch_rev + num_left == base + len - 1 - num_right < base + len.
            let dst_base = if towards_left { self.scratch_base } else { self.scratch_rev };
            let dst = dst_base.add(self.num_left);
            ptr::copy_nonoverlapping(self.scan, dst, 1);

            self.num_left += towards_left as usize;
            self.scan = self.scan.add(1);
            dst
        }
    }
}

trait IsFreeze {
    fn is_freeze() -> bool;
}

impl<T> IsFreeze for T {
    default fn is_freeze() -> bool {
        false
    }
}
impl<T: FreezeMarker> IsFreeze for T {
    fn is_freeze() -> bool {
        true
    }
}

#[must_use]
fn has_direct_interior_mutability<T>() -> bool {
    // If a type has interior mutability it may alter itself during comparison
    // in a way that must be preserved after the sort operation concludes.
    // Otherwise a type like Mutex<Option<Box<str>>> could lead to double free.
    !T::is_freeze()
}
#[cfg(kani)]
mod verify {
    use super::*;
    #[cfg(kani)]
    #[kani::proof_for_contract(quicksort)]
    fn proof_quicksort() {
        // Use a variable array size
        let size = 2 + (kani::any::<u8>() % 8) as usize;

        // Create an array to sort
        let mut data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..size {
            data[i] = kani::any();
        }

        // Calculate scratch size based on the requirement
        // scratch.len() >= max(v.len() - v.len() / 2, SMALL_SORT_GENERAL_SCRATCH_LEN)
        let min_scratch_size = size - size / 2;
        // Assuming SMALL_SORT_GENERAL_SCRATCH_LEN is a small constant
        let scratch_size = min_scratch_size + (kani::any::<u8>() as usize % 5);

        // Create a scratch space
        let mut scratch = [MaybeUninit::<i32>::uninit(); 10];

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Set up an arbitrary limit value
        let limit: u32 = 1 + kani::any::<u8>() as u32;

        // Set up a left ancestor pivot (None for initial call)
        let left_ancestor_pivot: Option<&i32> = None;

        // Call the function with valid inputs
        quicksort(
            &mut data[..size],
            &mut scratch[..scratch_size],
            limit,
            left_ancestor_pivot,
            &mut is_less,
        );
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(stable_partition)]
    fn proof_stable_partition() {
        // Use a variable array size
        let size = 2 + (kani::any::<u8>() % 8) as usize;

        // Create an array to partition
        let mut data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..size {
            data[i] = kani::any();
        }

        // Create a scratch space that's at least as large as the data array
        // Test both exact size and larger scratch spaces
        let scratch_size = size + (kani::any::<bool>() as usize * kani::any::<u8>() as usize % 5);
        let mut scratch = [MaybeUninit::<i32>::uninit(); 10];

        // Choose a pivot position that's within bounds
        let pivot_pos: usize = kani::any::<u8>() as usize % size;

        // Choose whether the pivot goes to the left or right
        let pivot_goes_left: bool = kani::any();

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        let _ = stable_partition(
            &mut data[..size],
            &mut scratch[..scratch_size],
            pivot_pos,
            pivot_goes_left,
            &mut is_less,
        );
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(new)]
    fn proof_partition_state_new() {
        // Use variable array sizes
        let scan_size = 2 + (kani::any::<u8>() % 8) as usize;
        let scratch_size = scan_size + (kani::any::<u8>() % 5) as usize;

        // Create two separate arrays
        let mut scan_data = [0i32; 10];
        let mut scratch_data = [0i32; 10];

        // Initialize scan data with arbitrary values
        for i in 0..scan_size {
            scan_data[i] = kani::any();
        }

        // Get pointers to the arrays
        let scan = scan_data.as_ptr();
        let scratch = scratch_data.as_mut_ptr();

        // Choose a length that's greater than 0 and at most scan_size
        // Test both edge cases and middle values
        let len: usize = if kani::any() {
            // Edge case: minimum length
            1
        } else if kani::any() {
            // Edge case: maximum length
            scan_size
        } else {
            // Middle value
            1 + (kani::any::<u8>() as usize % scan_size)
        };

        // Call the function with valid inputs
        unsafe {
            let _ = PartitionState::<i32>::new(scan, scratch, len);
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(partition_one)]
    fn proof_partition_one() {
        // Use a variable array size
        let size = 2 + (kani::any::<u8>() % 8) as usize;

        // Create two separate arrays
        let mut scan_data = [0i32; 10];
        let mut scratch_data = [0i32; 10];

        // Initialize scan data with arbitrary values
        for i in 0..size {
            scan_data[i] = kani::any();
        }

        // Get pointers to the arrays
        let scan = scan_data.as_ptr();
        let scratch_base = scratch_data.as_mut_ptr();

        // Choose a length that's greater than 0 and at most size
        let len: usize = 1 + (kani::any::<u8>() as usize % size);

        // Choose an arbitrary number of elements already processed
        // This simulates the state after some iterations
        let num_left = kani::any::<u8>() as usize % (len / 2 + 1);

        // Calculate how many elements have been scanned
        let scanned = kani::any::<u8>() as usize % (len - num_left + 1);

        unsafe {
            // Create a PartitionState with valid pointers
            let mut state = PartitionState {
                scratch_base,
                scan: scan.add(scanned),
                num_left,
                scratch_rev: scratch_base.add(len),
            };

            // Choose whether to partition towards left or right
            let towards_left: bool = kani::any();

            // Call the function with valid inputs
            let _ = state.partition_one(towards_left);
        }
    }
}
