// FIXME(static_mut_refs): Do not allow `static_mut_refs` lint
#![feature(ub_checks)]
#![allow(static_mut_refs)]

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
use core::kani;
#[allow(unused_imports)]
#[unstable(feature = "ub_checks", issue = "none")]
use core::ub_checks::*;
use safety::{ensures, requires};

use crate::alloc::{GlobalAlloc, Layout, System};

#[cfg(not(test))]
#[unsafe(export_name = "_ZN16__rust_internals3std3sys4xous5alloc8DLMALLOCE")]
static mut DLMALLOC: dlmalloc::Dlmalloc = dlmalloc::Dlmalloc::new();

#[cfg(test)]
unsafe extern "Rust" {
    #[link_name = "_ZN16__rust_internals3std3sys4xous5alloc8DLMALLOCE"]
    static mut DLMALLOC: dlmalloc::Dlmalloc;
}

#[stable(feature = "alloc_system_type", since = "1.28.0")]
unsafe impl GlobalAlloc for System {
    #[inline]
    #[requires(layout.size() <= isize::MAX as usize)]
    #[requires(layout.align().is_power_of_two())]
    #[requires(layout.size().checked_add(layout.align()).is_some())]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: DLMALLOC access is guaranteed to be safe because the lock gives us unique and non-reentrant access.
        // Calling malloc() is safe because preconditions on this function match the trait method preconditions.
        let _lock = lock::lock();
        unsafe { DLMALLOC.malloc(layout.size(), layout.align()) }
    }

    #[inline]
    #[requires(layout.size() <= isize::MAX as usize)]
    #[requires(layout.align().is_power_of_two())]
    #[requires(layout.size().checked_add(layout.align()).is_some())]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: DLMALLOC access is guaranteed to be safe because the lock gives us unique and non-reentrant access.
        // Calling calloc() is safe because preconditions on this function match the trait method preconditions.
        let _lock = lock::lock();
        unsafe { DLMALLOC.calloc(layout.size(), layout.align()) }
    }

    #[inline]
    #[requires(can_dereference(ptr) && can_read_unaligned(ptr.add(layout.size() - 1)))]
    #[requires(ptr as usize % layout.align() == 0)]
    #[requires(layout.size() <= isize::MAX as usize)]
    #[requires(layout.align().is_power_of_two())]
    #[requires(layout.size().checked_add(layout.align()).is_some())]
    #[cfg_attr(kani, kani::modifies(ptr))]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: DLMALLOC access is guaranteed to be safe because the lock gives us unique and non-reentrant access.
        // Calling free() is safe because preconditions on this function match the trait method preconditions.
        let _lock = lock::lock();
        unsafe { DLMALLOC.free(ptr, layout.size(), layout.align()) }
    }

    #[inline]
    #[requires(can_dereference(ptr) && can_read_unaligned(ptr.add(layout.size() - 1)))]
    #[requires(ptr as usize % layout.align() == 0)]
    #[requires(layout.size() <= isize::MAX as usize)]
    #[requires(new_size <= isize::MAX as usize)]
    #[requires(layout.align().is_power_of_two())]
    #[requires(layout.size().checked_add(layout.align()).is_some())]
    #[cfg_attr(kani, kani::modifies(ptr))]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: DLMALLOC access is guaranteed to be safe because the lock gives us unique and non-reentrant access.
        // Calling realloc() is safe because preconditions on this function match the trait method preconditions.
        let _lock = lock::lock();
        unsafe { DLMALLOC.realloc(ptr, layout.size(), layout.align(), new_size) }
    }
}

mod lock {
    use crate::sync::atomic::Ordering::{Acquire, Release};
    use crate::sync::atomic::{Atomic, AtomicI32};

    static LOCKED: Atomic<i32> = AtomicI32::new(0);

    pub struct DropLock;

    pub fn lock() -> DropLock {
        loop {
            if LOCKED.swap(1, Acquire) == 0 {
                return DropLock;
            }
            crate::os::xous::ffi::do_yield();
        }
    }

    impl Drop for DropLock {
        fn drop(&mut self) {
            let r = LOCKED.swap(0, Release);
            debug_assert_eq!(r, 1);
        }
    }
}
