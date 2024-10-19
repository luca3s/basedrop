use crate::{Handle, Node};

use core::marker::PhantomData;
use core::marker::SmartPointer;
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
#[derive(SmartPointer)]
#[repr(transparent)]
pub struct Owned<#[pointee] T: ?Sized> {
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

impl<T: ?Sized> Drop for Owned<T> {
    fn drop(&mut self) {
        unsafe {
            Node::queue_drop(self.node.as_ptr());
        }
    }
}

#[cfg(test)]
mod test {
    use core::any::Any;
    use crate::{Collector, Owned};

    #[test]
    fn unsize_dyn() {
        let mut collector = Collector::new();
        let shared: Owned<[u8]> = Owned::new(&collector.handle(), [0, 1, 2, 3]);
        let any: Owned<dyn Any> = Owned::new(&collector.handle(), 3u8);

        drop(shared);
        drop(any);
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }
}
