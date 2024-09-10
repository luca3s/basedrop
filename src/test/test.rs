mod test {
    #[test]
    fn dyn_test() {
        let collector = Collector::new();
        let handle = collector.handle();

        let normal = Owned::new(&handle, 0u8);

        let dyn_ptr: Owned<dyn Eq> = normal;
    }

    #[test]
    fn unsized_test() {
        let collector = Collector::new();
        let handle = collector.handle();

        let weird: Owned<[u8]>;
    }
}
