use core::alloc::Layout;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

extern crate alloc;
use alloc::boxed::Box;

#[repr(C)]
pub(crate) struct NodeHeader {
    link: NodeLink,
    /// stores the meta_data needed for unsized. With nightly feature ptr_metadata this could just be the metadata.
    /// initialized when the data is put into the drop queue. Needs the Node to not move, but this is already given with the library design
    /// Isn't `Node<T>` as that prohibits unsize coercion
    ///
    /// All fat pointers in Rust are the same size, so this works also for dyn. When PtrMetadata API is stablised this should use it.
    self_ptr: MaybeUninit<*mut [()]>,
    drop: unsafe fn(*mut NodeHeader),
}

impl NodeHeader {
    /// SAFETY: this ptr needs to be valid and self_ptr in NodeHeader has to be initialized.
    /// T has to be equal to T that the NodeHeader was initialized with.
    pub(crate) unsafe fn get_node_ptr<T: ?Sized>(this: *mut NodeHeader) -> *mut Node<T> {
        core::mem::transmute_copy(&(*this).self_ptr)
    }
}

#[repr(C)]
union NodeLink {
    collector: *mut CollectorInner,
    next: ManuallyDrop<AtomicPtr<NodeHeader>>,
}

/// An allocation that can be added to its associated [`Collector`]'s drop
/// queue.
///
/// `Node` provides a low-level interface intended for use in the
/// implementation of smart pointers and data structure internals. It is used
/// in the implementations of [`Owned`] and [`Shared`].
///
/// [`Collector`]: crate::Collector
/// [`Owned`]: crate::Owned
/// [`Shared`]: crate::Shared
#[repr(C)]
pub struct Node<T: ?Sized> {
    header: NodeHeader,
    /// The data stored in this allocation.
    pub data: T,
}

unsafe fn drop_node<T: ?Sized>(node: *mut NodeHeader) {
    // self_ptr is initialized by drop_node. If T: Sized only reads the first half of self_ptr. Rest is uninit
    let self_ptr = NodeHeader::get_node_ptr(node);
    let _: Box<Node<T>> = Box::from_raw(self_ptr);
}

impl<T: Send + 'static> Node<T> {
    /// Allocates a `Node` with the given data. Note that the `Node` will not
    /// be added to the drop queue or freed unless [`queue_drop`] is called.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Handle, Node};
    ///
    /// let mut collector = Collector::new();
    /// let handle = collector.handle();
    /// let node = Node::alloc(&handle, 3);
    /// ```
    ///
    /// [`queue_drop`]: crate::Node::queue_drop
    pub fn alloc(handle: &Handle, data: T) -> *mut Node<T> {
        unsafe {
            (*handle.collector).allocs.fetch_add(1, Ordering::Relaxed);
        }

        Box::into_raw(Box::new(Node {
            header: NodeHeader {
                link: NodeLink {
                    collector: handle.collector,
                },
                self_ptr: MaybeUninit::uninit(),
                drop: drop_node::<T>,
            },
            data,
        }))
    }
}

impl<T: Send + ?Sized + 'static> Node<T> {
    pub fn alloc_from_box(handle: &Handle, data: Box<T>) -> *mut Node<T> {
        unsafe {
            let src_ptr = &raw const *data;
            let node = Self::alloc_for_layout(handle, Layout::for_value(&*data), |mem| {
                // equivalent to ptr::with_metdata_of(other), but on stable
                let offset = mem.byte_offset_from(src_ptr);
                let src_ptr: *const Node<T> = src_ptr as *const Node<T>;
                src_ptr.byte_offset(offset).cast_mut()
            });

            let size = size_of_val(&*data);
            // move data
            core::ptr::copy_nonoverlapping(
                src_ptr as *const u8,
                (&raw mut (*node).data).cast(),
                size,
            );
            core::mem::forget(data);
            let src_ptr = src_ptr as *mut core::mem::ManuallyDrop<T>;
            let src: Box<ManuallyDrop<T>> = Box::from_raw(src_ptr);
            drop(src);
            node
        }
    }
}

impl<T: ?Sized> Node<T> {
    /// T in Node isn't initialized.
    /// This function increases the alloc counter of the collector.
    ///
    /// # convert_ptr
    /// needs to add any needed metadata. the returned ptr must point to the same location.
    /// This is needed to support creation of Node<Shared<T>>.
    pub(crate) unsafe fn alloc_for_layout(
        handle: &Handle,
        layout: Layout,
        // is a function, because then it can also create Shared Nodes
        convert_ptr: impl FnOnce(*mut u8) -> *mut Node<T>,
    ) -> *mut Node<T> {
        let node_layout = Layout::new::<Node<()>>()
            .extend(layout)
            .unwrap()
            .0
            .pad_to_align();

        // increase the alloc count directly before allocating
        unsafe {
            (*handle.collector).allocs.fetch_add(1, Ordering::Relaxed);
        }
        let mem_ptr = alloc::alloc::alloc(node_layout);
        if mem_ptr.is_null() {
            alloc::alloc::handle_alloc_error(node_layout);
        }

        let node_ptr = convert_ptr(mem_ptr);
        // debug assert that convert_ptr holds at least that requirement.
        debug_assert!(node_ptr.byte_offset_from(mem_ptr) == 0);

        // init the NodeHeader
        (&raw mut (*node_ptr).header).write(NodeHeader {
            link: NodeLink {
                collector: handle.collector,
            },
            drop: drop_node::<T>,
            self_ptr: MaybeUninit::uninit(),
        });
        node_ptr
    }

    /// Adds a `Node` to its associated [`Collector`]'s drop queue. The `Node`
    /// and its contained data may be dropped at a later time when
    /// [`Collector::collect`] or [`Collector::collect_one`] is called.
    ///
    /// The argument must point to a valid `Node` previously allocated with
    /// [`Node::alloc`]. `queue_drop` may only be called once for a given
    /// `Node`, and the `Node`'s data must not be accessed afterwards.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Handle, Node};
    ///
    /// let mut collector = Collector::new();
    /// let handle = collector.handle();
    /// let node = Node::alloc(&handle, 3);
    ///
    /// unsafe {
    ///     Node::queue_drop(node);
    /// }
    /// ```
    ///
    /// [`Collector`]: crate::Collector
    /// [`Collector::collect`]: crate::Collector::collect
    /// [`Collector::collect_one`]: crate::Collector::collect_one
    /// [`Node::alloc`]: crate::Node::alloc
    pub unsafe fn queue_drop(node: *mut Node<T>) {
        Self::write_self_ptr(node);
        let collector = (*node).header.link.collector;
        (*node).header.link.next = ManuallyDrop::new(AtomicPtr::new(core::ptr::null_mut()));
        let tail = (*collector).tail.swap(node as *mut NodeHeader, Ordering::AcqRel);
        (*tail).link.next.store(node as *mut NodeHeader, Ordering::Relaxed);
    }

    /// Prepare the node for being shared via AtomicPtr.
    /// Needed to drop it and to share it via SharedCell.
    /// Moving the Node after calling this method deinitializes self_ptr again.
    /// 
    /// SAFETY: node ptr needs to be valid.
    pub(crate) unsafe fn write_self_ptr(node: *mut Node<T>) {
        (*node)
            .header
            .self_ptr
            .as_mut_ptr()
            .cast::<*mut Node<T>>()
            .write(node);
    }

    /// Gets a [`Handle`] to this `Node`'s associated [`Collector`].
    ///
    /// The argument must point to a valid `Node` previously allocated with
    /// [`Node::alloc`], on which [`queue_drop`] has not been called.
    ///
    /// [`Handle`]: crate::Collector
    /// [`Collector`]: crate::Collector
    /// [`Node::alloc`]: crate::Node::alloc
    /// [`queue_drop`]: crate::Node::queue_drop
    pub unsafe fn handle(node: *mut Node<T>) -> Handle {
        let collector = (*node).header.link.collector;
        (*collector).handles.fetch_add(1, Ordering::Relaxed);
        Handle { collector }
    }
}

/// A handle to a [`Collector`], used when allocating [`Owned`] and [`Shared`]
/// values.
///
/// Multiple `Handle`s to a given [`Collector`] can exist at one time, and they
/// can be safely moved and shared between threads.
///
/// [`Collector`]: crate::Collector
/// [`Owned`]: crate::Owned
/// [`Shared`]: crate::Shared
pub struct Handle {
    collector: *mut CollectorInner,
}

unsafe impl Send for Handle {}
unsafe impl Sync for Handle {}

impl Clone for Handle {
    fn clone(&self) -> Self {
        unsafe {
            (*self.collector).handles.fetch_add(1, Ordering::Relaxed);
        }

        Handle { collector: self.collector }
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe {
            (*self.collector).handles.fetch_sub(1, Ordering::Release);
        }
    }
}

struct CollectorInner {
    handles: AtomicUsize,
    allocs: AtomicUsize,
    tail: AtomicPtr<NodeHeader>,
}

/// A garbage collector for [`Owned`] and [`Shared`] allocations.
///
/// If a `Collector` is dropped, it will leak all associated allocations as
/// well as its internal data structures. To avoid this, ensure that all
/// allocations have been collected and all [`Handle`]s have been dropped, then
/// call [`try_cleanup`].
///
/// [`Owned`]: crate::Owned
/// [`Shared`]: crate::Shared
/// [`try_cleanup`]: crate::Collector::try_cleanup
pub struct Collector {
    head: *mut NodeHeader,
    stub: *mut NodeHeader,
    inner: *mut CollectorInner,
}

unsafe impl Send for Collector {}

impl Collector {
    /// Constructs a new `Collector`.
    pub fn new() -> Collector {
        let head = Box::into_raw(Box::new(Node {
            header: NodeHeader {
                link: NodeLink {
                    next: ManuallyDrop::new(AtomicPtr::new(core::ptr::null_mut())),
                },
                self_ptr: MaybeUninit::uninit(),
                drop: drop_node::<()>,
            },
            data: (),
        })) as *mut NodeHeader;

        let inner = Box::into_raw(Box::new(CollectorInner {
            handles: AtomicUsize::new(0),
            allocs: AtomicUsize::new(0),
            tail: AtomicPtr::new(head),
        }));

        Collector {
            head,
            stub: head,
            inner,
        }
    }

    /// Gets a [`Handle`] to this `Collector`.
    ///
    /// [`Handle`]: crate::Handle
    pub fn handle(&self) -> Handle {
        unsafe {
            (*self.inner).handles.fetch_add(1, Ordering::Relaxed);
        }

        Handle { collector: self.inner }
    }

    /// Drops all of the garbage in the queue.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Handle, Owned};
    /// use core::mem::drop;
    ///
    /// let mut collector = Collector::new();
    /// let handle = collector.handle();
    /// let x = Owned::new(&handle, 1);
    /// let y = Owned::new(&handle, 2);
    /// let z = Owned::new(&handle, 3);
    ///
    /// assert_eq!(collector.alloc_count(), 3);
    ///
    /// drop(x);
    /// drop(y);
    /// drop(z);
    /// collector.collect();
    ///
    /// assert_eq!(collector.alloc_count(), 0);
    /// ```
    pub fn collect(&mut self) {
        while self.collect_one() {}
    }

    /// Attempts to drop the first allocation in the queue. If successful,
    /// returns true; otherwise returns false.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Handle, Owned};
    /// use core::mem::drop;
    ///
    /// let mut collector = Collector::new();
    /// let handle = collector.handle();
    /// let x = Owned::new(&handle, 1);
    /// let y = Owned::new(&handle, 2);
    /// let z = Owned::new(&handle, 3);
    ///
    /// assert_eq!(collector.alloc_count(), 3);
    ///
    /// drop(x);
    /// drop(y);
    /// drop(z);
    ///
    /// assert!(collector.collect_one());
    /// assert!(collector.collect_one());
    /// assert!(collector.collect_one());
    ///
    /// assert!(!collector.collect_one());
    /// assert_eq!(collector.alloc_count(), 0);
    /// ```
    pub fn collect_one(&mut self) -> bool {
        loop {
            unsafe {
                let next = (*self.head).link.next.load(Ordering::Acquire);
                if next.is_null() {
                    return false;
                }

                let head = self.head;
                self.head = next;
                if head == self.stub {
                    (*head).link.next.store(core::ptr::null_mut(), Ordering::Relaxed);
                    let tail = (*self.inner).tail.swap(head, Ordering::Release);
                    (*tail).link.next.store(head, Ordering::Relaxed);
                } else {
                    ((*head).drop)(head);
                    (*self.inner).allocs.fetch_sub(1, Ordering::Relaxed);
                    return true;
                }
            }
        }
    }

    /// Gets the number of live [`Handle`]s to this `Collector`.
    ///
    /// [`Handle`]: crate::Handle
    pub fn handle_count(&self) -> usize {
        unsafe { (*self.inner).handles.load(Ordering::Relaxed) }
    }

    /// Gets the number of live allocations associated with this `Collector`.
    pub fn alloc_count(&self) -> usize {
        unsafe { (*self.inner).allocs.load(Ordering::Relaxed) }
    }

    /// Attempts to free all resources associated with this `Collector`. This
    /// method will fail and return the original `Collector` if there are any
    /// live [`Handle`]s or allocations associated with it.
    ///
    /// # Examples
    /// ```
    /// use basedrop::{Collector, Handle, Owned};
    /// use core::mem::drop;
    ///
    /// let mut collector = Collector::new();
    /// let handle = collector.handle();
    /// let x = Owned::new(&handle, 3);
    ///
    /// let result = collector.try_cleanup();
    /// assert!(result.is_err());
    /// let mut collector = result.unwrap_err();
    ///
    /// drop(handle);
    /// drop(x);
    /// collector.collect();
    ///
    /// assert!(collector.try_cleanup().is_ok());
    /// ```
    ///
    /// [`Handle`]: crate::Handle
    pub fn try_cleanup(self) -> Result<(), Self> {
        unsafe {
            if (*self.inner).handles.load(Ordering::Acquire) == 0 {
                if (*self.inner).allocs.load(Ordering::Acquire) == 0 {
                    let _ = Box::from_raw(self.stub);
                    let _ = Box::from_raw(self.inner);

                    return Ok(());
                }
            }
        }

        Err(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate std;

    use alloc::sync::Arc;
    use core::sync::atomic::AtomicUsize;

    struct Test(Arc<AtomicUsize>);

    impl Drop for Test {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn unsize() {
        let mut collector = Collector::new();
        let node: *mut Node<[u8]> = Node::alloc(&collector.handle(), [0, 1, 2, 3]);
        unsafe { Node::queue_drop(node); }
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }

    #[test]
    fn dyn_coercion() {
        let mut collector = Collector::new();
        let node: *mut Node<dyn core::any::Any> = Node::alloc(&collector.handle(), 4u8);
        unsafe {
            Node::queue_drop(node);
        }
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }

    #[test]
    fn from_box() {
        let mut collector = Collector::new();
        let boxed_slice: Box<[i32]> = Box::new([0, 1, 2, 3]);
        let node = Node::alloc_from_box(&collector.handle(), boxed_slice);
        unsafe {
            Node::queue_drop(node);
        }
        collector.collect();
        assert!(collector.try_cleanup().is_ok());
    }

    #[test]
    fn collector() {
        let counter = Arc::new(AtomicUsize::new(0));

        let collector = Collector::new();
        let handle = collector.handle();

        let node = Node::alloc(&handle, ());
        let result = collector.try_cleanup();
        assert!(result.is_err());
        let mut collector = result.unwrap_err();
        unsafe {
            Node::queue_drop(node);
        }

        let mut threads = alloc::vec![];
        for _ in 0..100 {
            let handle = handle.clone();
            let counter = counter.clone();
            threads.push(std::thread::spawn(move || {
                for _ in 0..100 {
                    let node = Node::alloc(&handle, Test(counter.clone()));
                    unsafe {
                        Node::queue_drop(node);
                    }
                }
            }));
        }

        for _ in 0..100 {
            collector.collect();
        }

        for thread in threads {
            thread.join().unwrap();
        }

        collector.collect();

        let tail = unsafe { (*collector.inner).tail.load(Ordering::Relaxed) };
        assert!(collector.head == tail);
        assert!(collector.head == collector.stub);
        let next = unsafe { (*collector.head).link.next.load(Ordering::Relaxed) };
        assert!(next.is_null());

        assert!(counter.load(Ordering::Relaxed) == 10000);

        core::mem::drop(handle);

        let result = collector.try_cleanup();
        assert!(result.is_ok());
    }
}
