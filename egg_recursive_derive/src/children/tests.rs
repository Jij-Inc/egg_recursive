use super::*;
use crate::test_utils::*;

// ## Integrated Snapshots

#[test]
fn snapshot_derive_language_children_tuple() {
    let tt = apply_macro! {derive;
        priv struct Test<T>(T, [T; 3], Vec<T>, T);
    };
    insta::assert_snapshot!(tt);
}

#[test]
fn snapshot_derive_language_children_record() {
    let tt = apply_macro! {derive;
        pub struct Test<T>{myarg: T, clauses: [T; 3], variadics: Vec<T>, last: T}
    };
    insta::assert_snapshot!(tt);
}

// ## Part-wise snapshots

#[test]
fn snapshot_impl_tags() {
    let data = parse2::<DeriveInput>(quote! {
        struct MyChildren<T> {arg: T}
    })
    .unwrap();
    let info = ChildrenDeriver::try_new(data).unwrap();
    let orig = info.to_orig_impl_tag().pretty();
    insta::assert_snapshot!(orig, @r"
        ///The implementation tag of [`Functor`] for [`MyChildren`]. Generated via `#[derive(LanguageChildren)]`
        enum MyChildrenImpl {}
        ");

    let wrapper = info.to_wrapper_impl_tag().pretty();
    insta::assert_snapshot!(wrapper, @r"
        ///The implementation tag of [`Functor`] for [`RawMyChildren`]. Generated via `#[derive(LanguageChildren)]`
        enum RawMyChildrenImpl {}
        ");
}

#[test]
fn snapshot_to_orig_functor_tuple() {
    let data = parse2::<DeriveInput>(quote! {
        struct MyChildren<T>(T, [T; 3], Vec<T>, T, [T; 2]);
    })
    .unwrap();
    let info = ChildrenDeriver::try_new(data).unwrap();
    let tuple = info.to_orig_functor().pretty();
    insta::assert_snapshot!(tuple, @r"
        impl<T> MyChildren<T> {
            pub fn map<U, F>(self, mut f: F) -> MyChildren<U>
            where
                F: FnMut(T) -> U,
            {
                let Self { 0: fld_0, 1: fld_1, 2: fld_2, 3: fld_3, 4: fld_4 } = self;
                let fld_0 = f(fld_0);
                let fld_1 = fld_1.map(&mut f);
                let fld_2 = fld_2.into_iter().map(&mut f).collect();
                let fld_3 = f(fld_3);
                let fld_4 = fld_4.map(&mut f);
                MyChildren {
                    0: fld_0,
                    1: fld_1,
                    2: fld_2,
                    3: fld_3,
                    4: fld_4,
                }
            }
        }
        impl ::egg_recursive::Functor for MyChildrenImpl {
            type Container<T> = MyChildren<T>;
            fn fmap<A, B, F>(mut f: F, x: Self::Container<A>) -> Self::Container<B>
            where
                F: FnMut(A) -> B,
            {
                x.map(f)
            }
        }
        ");
}

#[test]
fn snapshot_to_orig_functor_record() {
    let data = parse2::<DeriveInput>(quote! {
        struct MyChildren<T> {
            head: T,
            tri: [T; 3],
            body: Vec<T>,
            last_two: [T; 2],
            tail_but_two: T,
        }
    })
    .unwrap();
    let info = ChildrenDeriver::try_new(data).unwrap();
    let rec = info.to_orig_functor().pretty();
    insta::assert_snapshot!(rec, @r"
        impl<T> MyChildren<T> {
            pub fn map<U, F>(self, mut f: F) -> MyChildren<U>
            where
                F: FnMut(T) -> U,
            {
                let Self { head, tri, body, last_two, tail_but_two } = self;
                let head = f(head);
                let tri = tri.map(&mut f);
                let body = body.into_iter().map(&mut f).collect();
                let last_two = last_two.map(&mut f);
                let tail_but_two = f(tail_but_two);
                MyChildren {
                    head,
                    tri,
                    body,
                    last_two,
                    tail_but_two,
                }
            }
        }
        impl ::egg_recursive::Functor for MyChildrenImpl {
            type Container<T> = MyChildren<T>;
            fn fmap<A, B, F>(mut f: F, x: Self::Container<A>) -> Self::Container<B>
            where
                F: FnMut(A) -> B,
            {
                x.map(f)
            }
        }
        ");
}

#[test]
fn snapshot_to_wrapper_type_fixed_size() {
    let record = parse2::<DeriveInput>(quote! {
        struct RecFixed<T> {
            head: T,
            tri: [T; 3],
            foo: T,
            bar: T,
            last_two: [T; 2],
            tail_but_two: T,
        }
    })
    .unwrap();
    let record = ChildrenDeriver::try_new(record).unwrap();
    let record = record.to_wrapper_type().pretty();
    insta::assert_snapshot!(record, @r"
        ///An array-like representation of [`RecFixed`], which is used with egg functions. Generated via `#[derive(LanguageChildren)]`
        #[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Hash, Clone, Debug)]
        struct RawRecFixed<T>([T; 9usize]);
        impl ::egg::LanguageChildren for RawRecFixed<::egg::Id> {
            fn len(&self) -> usize {
                self.0.len()
            }
            fn can_be_length(n: usize) -> bool {
                n == 9usize
            }
            fn from_vec(v: ::std::vec::Vec<::egg::Id>) -> Self {
                Self(<[::egg::Id; 9usize]>::try_from(v.as_slice()).unwrap())
            }
            fn as_slice(&self) -> &[::egg::Id] {
                self.0.as_slice()
            }
            fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                self.0.as_mut_slice()
            }
        }
        ");

    let tuple = parse2::<DeriveInput>(quote! {
        struct TupFixed<T> (T, [T; 4], T, [T; 2]);
    })
    .unwrap();
    let tuple = ChildrenDeriver::try_new(tuple).unwrap();
    let tuple = tuple.to_wrapper_type().pretty();
    insta::assert_snapshot!(tuple, @r"
        ///An array-like representation of [`TupFixed`], which is used with egg functions. Generated via `#[derive(LanguageChildren)]`
        #[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Hash, Clone, Debug)]
        struct RawTupFixed<T>([T; 8usize]);
        impl ::egg::LanguageChildren for RawTupFixed<::egg::Id> {
            fn len(&self) -> usize {
                self.0.len()
            }
            fn can_be_length(n: usize) -> bool {
                n == 8usize
            }
            fn from_vec(v: ::std::vec::Vec<::egg::Id>) -> Self {
                Self(<[::egg::Id; 8usize]>::try_from(v.as_slice()).unwrap())
            }
            fn as_slice(&self) -> &[::egg::Id] {
                self.0.as_slice()
            }
            fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                self.0.as_mut_slice()
            }
        }
        ");
}

#[test]
fn snapshot_to_wrapper_type_variadic_size() {
    let record = parse2::<DeriveInput>(quote! {
        struct RecFixed<T> {
            head: T,
            tri: [T; 3],
            foo: T,
            bar: T,
            var: Vec<T>,
            last_two: [T; 2],
            tail_but_two: T,
        }
    })
    .unwrap();
    let record = ChildrenDeriver::try_new(record).unwrap();
    let record = record.to_wrapper_type().pretty();
    insta::assert_snapshot!(record, @r"
        ///An array-like representation of [`RecFixed`], which is used with egg functions. Generated via `#[derive(LanguageChildren)]`
        #[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
        struct RawRecFixed<T>(::std::vec::Vec<T>);
        impl ::egg::LanguageChildren for RawRecFixed<::egg::Id> {
            fn len(&self) -> usize {
                self.0.len()
            }
            fn can_be_length(n: usize) -> bool {
                n >= 9usize
            }
            fn from_vec(v: Vec<::egg::Id>) -> Self {
                Self(v)
            }
            fn as_slice(&self) -> &[::egg::Id] {
                self.0.as_slice()
            }
            fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                self.0.as_mut_slice()
            }
        }
        ");

    let tuple = parse2::<DeriveInput>(quote! {
        struct TupFixed<T> (T, [T; 4], Vec<T>, [T; 2]);
    })
    .unwrap();
    let tuple = ChildrenDeriver::try_new(tuple).unwrap();
    let tuple = tuple.to_wrapper_type().pretty();
    insta::assert_snapshot!(tuple, @r"
        ///An array-like representation of [`TupFixed`], which is used with egg functions. Generated via `#[derive(LanguageChildren)]`
        #[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
        struct RawTupFixed<T>(::std::vec::Vec<T>);
        impl ::egg::LanguageChildren for RawTupFixed<::egg::Id> {
            fn len(&self) -> usize {
                self.0.len()
            }
            fn can_be_length(n: usize) -> bool {
                n >= 7usize
            }
            fn from_vec(v: Vec<::egg::Id>) -> Self {
                Self(v)
            }
            fn as_slice(&self) -> &[::egg::Id] {
                self.0.as_slice()
            }
            fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                self.0.as_mut_slice()
            }
        }
        ");
}

#[test]
fn spapshot_to_into_lang_children_fixed_size() {
    let record = parse2::<DeriveInput>(quote! {
        struct RecFixed<T> {
            head: T,
            foo: T,
            tri: [T; 3],
            last_two_but_one: [T; 2],
            last: T,
        }
    })
    .unwrap();
    let record = ChildrenDeriver::try_new(record).unwrap();
    let record = record.to_into_lang_children().pretty();
    insta::assert_snapshot!(record, @r#"
        impl<T> ::std::convert::From<RecFixed<T>> for RawRecFixed<T> {
            fn from(orig: RecFixed<T>) -> Self {
                let mut vec = Vec::new();
                vec.push(orig.head);
                vec.push(orig.foo);
                vec.extend(orig.tri);
                vec.extend(orig.last_two_but_one);
                vec.push(orig.last);
                Self(vec.try_into().map_err(|_| "impossible").unwrap())
            }
        }
        impl<T> ::std::convert::From<RawRecFixed<T>> for RecFixed<T> {
            fn from(wrapper: RawRecFixed<T>) -> Self {
                let mut iter = wrapper.0.into_iter();
                Self {
                    head: iter.next().unwrap(),
                    foo: iter.next().unwrap(),
                    tri: iter
                        .by_ref()
                        .take(3usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    last_two_but_one: iter
                        .by_ref()
                        .take(2usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    last: iter.next().unwrap(),
                }
            }
        }
        impl<T> ::egg_recursive::IntoLanguageChildren for RecFixed<T> {
            type View = RecFixedImpl;
            type RawData = RawRecFixedImpl;
            type Param = T;
            fn unview<U>(input: RecFixed<U>) -> RawRecFixed<U> {
                input.into()
            }
            fn view<U>(wrapper: RawRecFixed<U>) -> RecFixed<U> {
                wrapper.into()
            }
            fn raw_as_refs<'a, U>(input: &'a RawRecFixed<U>) -> RawRecFixed<&'a U> {
                let RawRecFixed(input) = input;
                let input = input.each_ref();
                RawRecFixed(input)
            }
        }
        impl<T> RawRecFixed<T> {
            pub fn view(self) -> RecFixed<T> {
                self.into()
            }
        }
        impl<T> RecFixed<T> {
            pub fn unview(self) -> RawRecFixed<T> {
                self.into()
            }
        }
        "#);

    let tuple = parse2::<DeriveInput>(quote! {
        struct TupFixed<T> (T, [T; 4], T, T, [T; 2]);
    })
    .unwrap();
    let tuple = ChildrenDeriver::try_new(tuple).unwrap();
    let tuple = tuple.to_into_lang_children().pretty();
    insta::assert_snapshot!(tuple, @r#"
        impl<T> ::std::convert::From<TupFixed<T>> for RawTupFixed<T> {
            fn from(orig: TupFixed<T>) -> Self {
                let mut vec = Vec::new();
                vec.push(orig.0);
                vec.extend(orig.1);
                vec.push(orig.2);
                vec.push(orig.3);
                vec.extend(orig.4);
                Self(vec.try_into().map_err(|_| "impossible").unwrap())
            }
        }
        impl<T> ::std::convert::From<RawTupFixed<T>> for TupFixed<T> {
            fn from(wrapper: RawTupFixed<T>) -> Self {
                let mut iter = wrapper.0.into_iter();
                Self {
                    0: iter.next().unwrap(),
                    1: iter
                        .by_ref()
                        .take(4usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    2: iter.next().unwrap(),
                    3: iter.next().unwrap(),
                    4: iter
                        .by_ref()
                        .take(2usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                }
            }
        }
        impl<T> ::egg_recursive::IntoLanguageChildren for TupFixed<T> {
            type View = TupFixedImpl;
            type RawData = RawTupFixedImpl;
            type Param = T;
            fn unview<U>(input: TupFixed<U>) -> RawTupFixed<U> {
                input.into()
            }
            fn view<U>(wrapper: RawTupFixed<U>) -> TupFixed<U> {
                wrapper.into()
            }
            fn raw_as_refs<'a, U>(input: &'a RawTupFixed<U>) -> RawTupFixed<&'a U> {
                let RawTupFixed(input) = input;
                let input = input.each_ref();
                RawTupFixed(input)
            }
        }
        impl<T> RawTupFixed<T> {
            pub fn view(self) -> TupFixed<T> {
                self.into()
            }
        }
        impl<T> TupFixed<T> {
            pub fn unview(self) -> RawTupFixed<T> {
                self.into()
            }
        }
        "#);
}

#[test]
fn spapshot_to_into_lang_children_variadic_size() {
    let record = parse2::<DeriveInput>(quote! {
        struct RecFixed<T> {
            ini: Vec<T>,
            head: T,
            tri: [T; 3],
            last_two_but_one: [T; 2],
            last: T,
        }
    })
    .unwrap();
    let record = ChildrenDeriver::try_new(record).unwrap();
    let record = record.to_into_lang_children().pretty();
    insta::assert_snapshot!(record, @r#"
        impl<T> ::std::convert::From<RecFixed<T>> for RawRecFixed<T> {
            fn from(orig: RecFixed<T>) -> Self {
                let mut vec = Vec::new();
                vec.extend(orig.ini);
                vec.push(orig.head);
                vec.extend(orig.tri);
                vec.extend(orig.last_two_but_one);
                vec.push(orig.last);
                Self(vec.try_into().map_err(|_| "impossible").unwrap())
            }
        }
        impl<T> ::std::convert::From<RawRecFixed<T>> for RecFixed<T> {
            fn from(wrapper: RawRecFixed<T>) -> Self {
                let len = wrapper.0.len();
                let mut iter = wrapper.0.into_iter();
                Self {
                    ini: iter.by_ref().take(len - 7usize).collect(),
                    head: iter.next().unwrap(),
                    tri: iter
                        .by_ref()
                        .take(3usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    last_two_but_one: iter
                        .by_ref()
                        .take(2usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    last: iter.next().unwrap(),
                }
            }
        }
        impl<T> ::egg_recursive::IntoLanguageChildren for RecFixed<T> {
            type View = RecFixedImpl;
            type RawData = RawRecFixedImpl;
            type Param = T;
            fn unview<U>(input: RecFixed<U>) -> RawRecFixed<U> {
                input.into()
            }
            fn view<U>(wrapper: RawRecFixed<U>) -> RecFixed<U> {
                wrapper.into()
            }
            fn raw_as_refs<'a, U>(input: &'a RawRecFixed<U>) -> RawRecFixed<&'a U> {
                let RawRecFixed(input) = input;
                let input = input.iter().collect();
                RawRecFixed(input)
            }
        }
        impl<T> RawRecFixed<T> {
            pub fn view(self) -> RecFixed<T> {
                self.into()
            }
        }
        impl<T> RecFixed<T> {
            pub fn unview(self) -> RawRecFixed<T> {
                self.into()
            }
        }
        "#);

    let tuple = parse2::<DeriveInput>(quote! {
        struct TupFixed<T> (T, Vec<T>, [T; 4], T, T, [T; 2]);
    })
    .unwrap();
    let tuple = ChildrenDeriver::try_new(tuple).unwrap();
    let tuple = tuple.to_into_lang_children().pretty();
    insta::assert_snapshot!(tuple, @r#"
        impl<T> ::std::convert::From<TupFixed<T>> for RawTupFixed<T> {
            fn from(orig: TupFixed<T>) -> Self {
                let mut vec = Vec::new();
                vec.push(orig.0);
                vec.extend(orig.1);
                vec.extend(orig.2);
                vec.push(orig.3);
                vec.push(orig.4);
                vec.extend(orig.5);
                Self(vec.try_into().map_err(|_| "impossible").unwrap())
            }
        }
        impl<T> ::std::convert::From<RawTupFixed<T>> for TupFixed<T> {
            fn from(wrapper: RawTupFixed<T>) -> Self {
                let len = wrapper.0.len();
                let mut iter = wrapper.0.into_iter();
                Self {
                    0: iter.next().unwrap(),
                    1: iter.by_ref().take(len - 9usize).collect(),
                    2: iter
                        .by_ref()
                        .take(4usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                    3: iter.next().unwrap(),
                    4: iter.next().unwrap(),
                    5: iter
                        .by_ref()
                        .take(2usize)
                        .collect::<Vec<_>>()
                        .try_into()
                        .map_err(|_| "impossible")
                        .unwrap(),
                }
            }
        }
        impl<T> ::egg_recursive::IntoLanguageChildren for TupFixed<T> {
            type View = TupFixedImpl;
            type RawData = RawTupFixedImpl;
            type Param = T;
            fn unview<U>(input: TupFixed<U>) -> RawTupFixed<U> {
                input.into()
            }
            fn view<U>(wrapper: RawTupFixed<U>) -> TupFixed<U> {
                wrapper.into()
            }
            fn raw_as_refs<'a, U>(input: &'a RawTupFixed<U>) -> RawTupFixed<&'a U> {
                let RawTupFixed(input) = input;
                let input = input.iter().collect();
                RawTupFixed(input)
            }
        }
        impl<T> RawTupFixed<T> {
            pub fn view(self) -> TupFixed<T> {
                self.into()
            }
        }
        impl<T> TupFixed<T> {
            pub fn unview(self) -> RawTupFixed<T> {
                self.into()
            }
        }
        "#);
}
