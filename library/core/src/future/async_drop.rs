#![unstable(feature = "async_drop", issue = "126482")]

#[allow(unused_imports)]
use safety::{ensures,requires};
#[cfg(kani)]
use crate::kani;
#[allow(unused_imports)]
use crate::ub_checks::*;

use core::future::Future;

#[allow(unused_imports)]
use crate::pin::Pin;
#[allow(unused_imports)]
use crate::task::{Context, Poll};

/// Async version of Drop trait.
///
/// When a value is no longer needed, Rust will run a "destructor" on that value.
/// The most common way that a value is no longer needed is when it goes out of
/// scope. Destructors may still run in other circumstances, but we're going to
/// focus on scope for the examples here. To learn about some of those other cases,
/// please see [the reference] section on destructors.
///
/// [the reference]: https://doc.rust-lang.org/reference/destructors.html
///
/// ## `Copy` and ([`Drop`]|`AsyncDrop`) are exclusive
///
/// You cannot implement both [`Copy`] and ([`Drop`]|`AsyncDrop`) on the same type. Types that
/// are `Copy` get implicitly duplicated by the compiler, making it very
/// hard to predict when, and how often destructors will be executed. As such,
/// these types cannot have destructors.
#[unstable(feature = "async_drop", issue = "126482")]
#[lang = "async_drop"]
pub trait AsyncDrop {
    /// Executes the async destructor for this type.
    ///
    /// This method is called implicitly when the value goes out of scope,
    /// and cannot be called explicitly.
    ///
    /// When this method has been called, `self` has not yet been deallocated.
    /// That only happens after the method is over.
    ///
    /// # Panics
    #[allow(async_fn_in_trait)]
    async fn drop(self: Pin<&mut Self>);
}

/// Async drop.
#[unstable(feature = "async_drop", issue = "126482")]
#[lang = "async_drop_in_place"]
pub async unsafe fn async_drop_in_place<T: ?Sized>(_to_drop: *mut T) {
    // Code here does not matter - this is replaced by the
    // real implementation by the compiler.
}
#[cfg(kani)] mod verify {use super::*;

#[kani::proof_for_contract(async_drop_in_place)]
async fn proof_for_contract_async_drop_in_place() {
    // Create a simple type that can be dropped
    struct SimpleType {
        value: i32,
    }
    
    // Allocate memory for our test object
    let mut value = SimpleType { value: kani::any::<i32>() };
    
    // Get a raw pointer to the value
    let ptr = &mut value as *mut SimpleType;
    
    // Call the function with the pointer
    // The precondition is satisfied because ptr points to a valid object
    unsafe {
        async_drop_in_place(ptr).await;
    }
}
}