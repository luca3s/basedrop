use crate::{Handle, Node};
use core::alloc::Layout;
use core::marker::SmartPointer;

use core::marker::PhantomData;
use core::ops::Deref;

use core::ptr::NonNull;
use core::sync::atomic::{AtomicUsize, Ordering, fence};

extern crate alloc;
use alloc::boxed::Box;

/// A reference-counted smart pointer with deferred collection, analogous to
/// `Arc`.
///
/// When a `Shared<T>`'s reference count goes to zero, its contents are added
/// to the drop queue of the [`Collector`] whose [`Handle`] it was originally
/// allocated with. As the collector may be on another thread, contents are
/// required to be `Send + 'static`.
///
/// [`Collector`]: crate::Collector
/// [`Handle`]: crate::Handle
#[derive(SmartPointer)]
#[repr(transparent)]
pub struct Shared<#[pointee] T: ?Sized> {
    pub(crate) node: NonNull<Node<SharedInner<T>>>,
    pub(crate) phantom: PhantomData<SharedInner<T>>,
}

pub(crate) struct SharedInner<T: ?Sized> {
    count: AtomicUsize,
    data: T,
}

unsafe impl<T: Send + Sync + ?Sized> Send for Shared<T> {}
unsafe impl<T: Send + Sync + ?Sized> Sync for Shared<T> {}

impl<T: Send + 'static> Shared<T> {
    /// Constructs a new `Shared<T>`.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Shared};
    ///
    /// let collector = Collector::new();
    /// let three = Shared::new(&collector.handle(), 3);
    /// ```
    pub fn new(handle: &Handle, data: T) -> Shared<T> {
        Shared {
            node: unsafe {
                NonNull::new_unchecked(Node::alloc(handle, SharedInner {
                    count: AtomicUsize::new(1),
                    data,
                }))
            },
            phantom: PhantomData,
        }
    }
}

impl<T: Send + ?Sized + 'static> Shared<T> {
    pub fn from_box(handle: &Handle, data: Box<T>) -> Self {
        unsafe {
            let src_ptr = &raw const *data;
            let node = Node::<SharedInner<T>>::alloc_for_layout(
                handle,
                Layout::for_value(&*data),
                |mem| {
                    // equivalent to ptr::with_metdata_of(other), but on stable
                    let offset = mem.byte_offset_from(src_ptr);
                    let src_ptr = src_ptr as *const Node<SharedInner<T>>;
                    src_ptr.byte_offset(offset).cast_mut()
                },
            );

            // init the share count
            (&raw mut (*node).data.count).write(AtomicUsize::new(1));
            // copy the data
            core::ptr::copy_nonoverlapping(
                src_ptr as *const u8,
                (&raw mut (*node).data.data) as *mut u8,
                size_of_val(&*data),
            );
            // drop the box, without dropping the value inside the box
            core::mem::forget(data);
            let src = Box::from_raw(src_ptr as *mut core::mem::ManuallyDrop<T>);
            drop(src);

            Shared {
                node: NonNull::new_unchecked(node),
                phantom: PhantomData,
            }
        }
    }
}

impl<T: ?Sized> Shared<T> {
    /// Returns a mutable reference to the contained value if there are no
    /// other extant `Shared` pointers to the same allocation; otherwise
    /// returns `None`.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Shared};
    ///
    /// let collector = Collector::new();
    /// let mut x = Shared::new(&collector.handle(), 3);
    ///
    /// *Shared::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// let _y = Shared::clone(&x);
    /// assert!(Shared::get_mut(&mut x).is_none());
    /// ```
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        unsafe {
            if this.node.as_ref().data.count.load(Ordering::Acquire) == 1 {
                Some(&mut this.node.as_mut().data.data)
            } else {
                None
            }
        }
    }
}

impl<T: ?Sized> Clone for Shared<T> {
    fn clone(&self) -> Self {
        unsafe {
            self.node.as_ref().data.count.fetch_add(1, Ordering::Relaxed);
        }

        Shared { node: self.node, phantom: PhantomData }
    }
}

impl<T: ?Sized> Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.node.as_ref().data.data }
    }
}

impl<T: ?Sized> Drop for Shared<T> {
    fn drop(&mut self) {
        unsafe {
            let count = self.node.as_ref().data.count.fetch_sub(1, Ordering::Release);

            if count == 1 {
                fence(Ordering::Acquire);
                Node::queue_drop(self.node.as_ptr());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Collector, Shared};

    extern crate alloc;

    use core::{
        any::Any,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use alloc::boxed::Box;

    #[test]
    fn unsize_dyn() {
        let mut collector = Collector::new();
        let shared: Shared<[u8]> = Shared::new(&collector.handle(), [0, 1, 2, 3]);
        let any: Shared<dyn Any> = Shared::new(&collector.handle(), 3u8);

        drop(shared);
        drop(any);
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }

    #[test]
    fn from_unsize_box() {
        let mut collector = Collector::new();
        let slice_box: Box<[i32]> = Box::new([0, 1, 2, 3]);

        // here the trait needs to require T: Send. otherwise creation of Shared not possible.
        // when a useful trait is wanted it should be implemented by requiring Send on every implementor of the trait
        // or by creating a dummy trait that just combines Send with the wanted trait
        let dyn_box: Box<dyn Send> = Box::new(25);

        let shared_slice = Shared::from_box(&collector.handle(), slice_box);
        let shared_dyn = Shared::from_box(&collector.handle(), dyn_box);

        drop(shared_slice);
        drop(shared_dyn);
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }

    #[test]
    fn shared() {
        extern crate alloc;
        use alloc::sync::Arc;

        struct Test(Arc<AtomicUsize>);

        impl Drop for Test {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }

        let counter = Arc::new(AtomicUsize::new(0));

        let mut collector = Collector::new();
        let handle = collector.handle();

        let shared = Shared::new(&handle, Test(counter.clone()));
        let mut copies = alloc::vec::Vec::new();
        for _ in 0..10 {
            copies.push(shared.clone());
        }

        assert_eq!(counter.load(Ordering::Relaxed), 0);

        core::mem::drop(shared);
        core::mem::drop(copies);
        collector.collect();

        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn get_mut() {
        let collector = Collector::new();
        let mut x = Shared::new(&collector.handle(), 3);

        *Shared::get_mut(&mut x).unwrap() = 4;
        assert_eq!(*x, 4);

        let _y = Shared::clone(&x);
        assert!(Shared::get_mut(&mut x).is_none());
    }
}
