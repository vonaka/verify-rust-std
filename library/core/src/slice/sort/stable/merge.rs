//! This module contains logic for performing a merge of two sorted sub-slices.

use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use crate::mem::MaybeUninit;
use crate::{cmp, ptr};

/// Merges non-decreasing runs `v[..mid]` and `v[mid..]` using `scratch` as
/// temporary storage, and stores the result into `v[..]`.
#[requires(scratch.len() >= cmp::min(mid, v.len() - mid))]
#[requires(mid <= v.len())]
#[cfg_attr(kani, kani::modifies(v.as_mut_ptr()))]
#[cfg_attr(kani, kani::modifies(scratch.as_mut_ptr()))]
pub fn merge<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    mid: usize,
    is_less: &mut F,
) {
    let len = v.len();

    if mid == 0 || mid >= len || scratch.len() < cmp::min(mid, len - mid) {
        return;
    }

    // SAFETY: We checked that the two slices are non-empty and `mid` is in-bounds.
    // We checked that the buffer `scratch` has enough capacity to hold a copy of
    // the shorter slice. `merge_up` and `merge_down` are written in such a way that
    // they uphold the contract described in `MergeState::drop`.
    unsafe {
        // The merge process first copies the shorter run into `buf`. Then it traces
        // the newly copied run and the longer run forwards (or backwards), comparing
        // their next unconsumed elements and copying the lesser (or greater) one into `v`.
        //
        // As soon as the shorter run is fully consumed, the process is done. If the
        // longer run gets consumed first, then we must copy whatever is left of the
        // shorter run into the remaining gap in `v`.
        //
        // Intermediate state of the process is always tracked by `gap`, which serves
        // two purposes:
        //  1. Protects integrity of `v` from panics in `is_less`.
        //  2. Fills the remaining gap in `v` if the longer run gets consumed first.

        let buf = MaybeUninit::slice_as_mut_ptr(scratch);

        let v_base = v.as_mut_ptr();
        let v_mid = v_base.add(mid);
        let v_end = v_base.add(len);

        let left_len = mid;
        let right_len = len - mid;

        let left_is_shorter = left_len <= right_len;
        let save_base = if left_is_shorter { v_base } else { v_mid };
        let save_len = if left_is_shorter { left_len } else { right_len };

        ptr::copy_nonoverlapping(save_base, buf, save_len);

        let mut merge_state = MergeState { start: buf, end: buf.add(save_len), dst: save_base };

        if left_is_shorter {
            merge_state.merge_up(v_mid, v_end, is_less);
        } else {
            merge_state.merge_down(v_base, buf, v_end, is_less);
        }
        // Finally, `merge_state` gets dropped. If the shorter run was not fully
        // consumed, whatever remains of it will now be copied into the hole in `v`.
    }
}

// When dropped, copies the range `start..end` into `dst..`.
struct MergeState<T> {
    start: *mut T,
    end: *mut T,
    dst: *mut T,
}

impl<T> MergeState<T> {
    /// # Safety
    /// The caller MUST guarantee that `self` is initialized in a way where `start -> end` is
    /// the longer sub-slice and so that `dst` can be written to at least the shorter sub-slice
    /// length times. In addition `start -> end` and `right -> right_end` MUST be valid to be
    /// read. This function MUST only be called once.
    #[requires(self.start <= self.end)]
    #[requires(can_dereference(self.start) && can_dereference(self.end))]
    #[requires(can_dereference(right) && can_dereference(right_end))]
    #[requires(can_write(self.dst))]
    #[requires(!same_allocation(self.dst, right))]
    #[requires(can_write(self.dst.add(i)) for i in 0..cmp::min(self.end.offset_from(self.start), right_end.offset_from(right)))]
    unsafe fn merge_up<F: FnMut(&T, &T) -> bool>(
        &mut self,
        mut right: *const T,
        right_end: *const T,
        is_less: &mut F,
    ) {
        // SAFETY: See function safety comment.
        unsafe {
            let left = &mut self.start;
            let out = &mut self.dst;

            while *left != self.end && right as *const T != right_end {
                let consume_left = !is_less(&*right, &**left);

                let src = if consume_left { *left } else { right };
                ptr::copy_nonoverlapping(src, *out, 1);

                *left = left.add(consume_left as usize);
                right = right.add(!consume_left as usize);

                *out = out.add(1);
            }
        }
    }

    /// # Safety
    /// The caller MUST guarantee that `self` is initialized in a way where `left_end <- dst` is
    /// the shorter sub-slice and so that `out` can be written to at least the shorter sub-slice
    /// length times. In addition `left_end <- dst` and `right_end <- end` MUST be valid to be
    /// read. This function MUST only be called once.
    #[requires(self.start <= self.end)]
    #[requires(can_dereference(left_end) && can_dereference(right_end))]
    #[requires(can_dereference(self.start) && can_dereference(self.end))]
    #[requires(can_write(out))]
    #[requires(!same_allocation(out, self.start) && !same_allocation(out, self.end))]
    #[requires(can_write(out.sub(i)) for i in 1..=cmp::min(self.end.offset_from(self.start), self.end.offset_from(right_end)))]
    unsafe fn merge_down<F: FnMut(&T, &T) -> bool>(
        &mut self,
        left_end: *const T,
        right_end: *const T,
        mut out: *mut T,
        is_less: &mut F,
    ) {
        // SAFETY: See function safety comment.
        unsafe {
            loop {
                let left = self.dst.sub(1);
                let right = self.end.sub(1);
                out = out.sub(1);

                let consume_left = is_less(&*right, &*left);

                let src = if consume_left { left } else { right };
                ptr::copy_nonoverlapping(src, out, 1);

                self.dst = left.add(!consume_left as usize);
                self.end = right.add(consume_left as usize);

                if self.dst as *const T == left_end || self.end as *const T == right_end {
                    break;
                }
            }
        }
    }
}

impl<T> Drop for MergeState<T> {
    #[requires(can_dereference(self.start) && can_dereference(self.end))]
    #[requires(can_write(self.dst))]
    #[requires(self.end.offset_from(self.start) >= 0)]
    #[cfg_attr(kani, kani::modifies(self.dst))]
    fn drop(&mut self) {
        // SAFETY: The user of MergeState MUST ensure, that at any point this drop
        // impl MAY run, for example when the user provided `is_less` panics, that
        // copying the contiguous region between `start` and `end` to `dst` will
        // leave the input slice `v` with each original element and all possible
        // modifications observed.
        unsafe {
            let len = self.end.offset_from_unsigned(self.start);
            ptr::copy_nonoverlapping(self.start, self.dst, len);
        }
    }
}
#[cfg(kani)]
mod verify {
    use super::*;
    #[cfg(kani)]
    #[kani::proof_for_contract(merge)]
    fn proof_merge() {
        // Use a variable array size
        let array_size = 2 + (kani::any::<u8>() % 8) as usize;

        // Create an array to work with
        let mut data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..array_size {
            data[i] = kani::any();
        }

        // Choose a mid point that's within bounds
        let mid: usize = 1 + (kani::any::<u8>() as usize % (array_size - 1));

        // Calculate the minimum required scratch space size
        let scratch_size = cmp::min(mid, array_size - mid);

        // Create a scratch space with safer initialization
        let mut scratch = [MaybeUninit::<i32>::uninit(); 10];

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        merge(
            &mut data[..array_size],
            &mut scratch[..array_size],
            mid,
            &mut is_less,
        );
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(merge_up)]
    fn proof_merge_up() {
        // Use variable array sizes
        let left_size = 2 + (kani::any::<u8>() % 3) as usize;
        let right_size = 2 + (kani::any::<u8>() % 3) as usize;

        // Create arrays for left, right, and destination
        let mut left_data = [0i32; 5];
        let mut right_data = [0i32; 5];
        let mut dst_data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..left_size {
            left_data[i] = kani::any();
        }
        for i in 0..right_size {
            right_data[i] = kani::any();
        }

        // Get pointers to the arrays
        let left_start = left_data.as_mut_ptr();
        let left_end = unsafe { left_start.add(left_size) };
        let right_start = right_data.as_ptr();
        let right_end = unsafe { right_start.add(right_size) };
        let dst = dst_data.as_mut_ptr();

        // Create a MergeState with valid pointers
        let mut merge_state = MergeState {
            start: left_start,
            end: left_end,
            dst: dst,
        };

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        unsafe {
            merge_state.merge_up(right_start, right_end, &mut is_less);
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(merge_down)]
    fn proof_merge_down() {
        // Use variable array sizes
        let left_size = 2 + (kani::any::<u8>() % 3) as usize;
        let right_size = 2 + (kani::any::<u8>() % 3) as usize;
        let dst_size = left_size + right_size;

        // Create arrays for left, right, and destination
        let mut left_data = [0i32; 5];
        let mut right_data = [0i32; 5];
        let mut dst_data = [0i32; 10];

        // Initialize with arbitrary values
        for i in 0..left_size {
            left_data[i] = kani::any();
        }
        for i in 0..right_size {
            right_data[i] = kani::any();
        }

        // Get pointers to the arrays
        let left_start = left_data.as_mut_ptr();
        let left_end = unsafe { left_start.add(left_size) };
        let right_start = right_data.as_mut_ptr();
        let right_end = unsafe { right_start.add(right_size) };

        // For merge_down, ensure we have a valid output pointer
        let out_base = dst_data.as_mut_ptr();
        let out = unsafe { out_base.add(dst_size - 1) };

        // Create a MergeState with valid pointers
        let mut merge_state = MergeState {
            start: right_start,
            end: right_end,
            dst: left_end, // This is just a placeholder, not used in merge_down
        };

        // Create a comparison function
        let mut is_less = |x: &i32, y: &i32| -> bool { x < y };

        // Call the function with valid inputs
        unsafe {
            merge_state.merge_down(left_end, right_end, out, &mut is_less);
        }
    }

    #[cfg(kani)]
    #[kani::proof_for_contract(drop)]
    fn proof_drop() {
        // Use a variable array size
        let size = 2 + (kani::any::<u8>() % 4) as usize;

        // Create arrays for source and destination
        let mut src_data = [0i32; 5];
        let mut dst_data = [0i32; 5];

        // Initialize with arbitrary values
        for i in 0..size {
            src_data[i] = kani::any();
        }

        // Get pointers to the arrays
        let start = src_data.as_mut_ptr();
        let end = unsafe { start.add(size) };
        let dst = dst_data.as_mut_ptr();

        // Create a MergeState with valid pointers
        let merge_state = MergeState {
            start: start,
            end: end,
            dst: dst,
        };

        // Explicitly drop the merge_state to test the drop implementation
        std::mem::drop(merge_state);
    }
}
