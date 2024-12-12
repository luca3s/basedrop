use crate::{Handle, Node};

use core::fmt::Debug;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

extern crate alloc;

/// An owned smart pointer with deferred collection, analogous to `Box`.
///
/// When an `Owned<T>` is dropped, its contents are added to the drop queue
/// of the [`Collector`] whose [`Handle`] it was originally allocated with.
/// As the collector may be on another thread, contents are required to be
/// `Send + 'static`.
///
/// [`Collector`]: crate::Collector
/// [`Handle`]: crate::Handle
#[repr(transparent)]
pub struct Owned<T: ?Sized> {
    node: NonNull<Node<T>>,
    phantom: PhantomData<T>,
}

unsafe impl<T: Send + ?Sized> Send for Owned<T> {}
unsafe impl<T: Sync + ?Sized> Sync for Owned<T> {}

impl<T: Send + 'static> Owned<T> {
    /// Constructs a new `Owned<T>`.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Owned};
    ///
    /// let collector = Collector::new();
    /// let three = Owned::new(&collector.handle(), 3);
    /// ```
    pub fn new(handle: &Handle, data: T) -> Owned<T> {
        Owned {
            node: unsafe { NonNull::new_unchecked(Node::alloc(handle, data)) },
            phantom: PhantomData,
        }
    }
}

impl<T: Send + ?Sized + 'static> Owned<T> {
    pub fn from_box(handle: &Handle, data: alloc::boxed::Box<T>) -> Self {
        Owned {
            node: unsafe { NonNull::new_unchecked(Node::alloc_from_box(handle, data)) },
            phantom: PhantomData
        }
    }
}

impl<T: Clone + Send + 'static> Clone for Owned<T> {
    fn clone(&self) -> Self {
        let handle = unsafe { Node::handle(self.node.as_ptr()) };
        Owned::new(&handle, self.deref().clone())
    }
}

impl<T: ?Sized> Deref for Owned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.node.as_ref().data }
    }
}

impl<T: ?Sized> DerefMut for Owned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.node.as_mut().data }
    }
}

impl<T: Debug + ?Sized> Debug for Owned<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Owned").field("value", &self.deref()).finish()
    }
}

impl<T: ?Sized> Drop for Owned<T> {
    fn drop(&mut self) {
        unsafe {
            Node::queue_drop(self.node.as_ptr());
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate alloc;

    use core::fmt::Write;

    use crate::{Collector, Owned};

    #[test]
    fn debug() {
        let collector = Collector::new();
        let x = Owned::new(&collector.handle(), 3);

        let mut w = alloc::string::String::new();
        write!(&mut w, "{x:?}").unwrap();
        assert_eq!(w, "Owned { value: 3 }");
    }
}