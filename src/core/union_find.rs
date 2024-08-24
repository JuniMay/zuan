//! # Union-find Data Structure
//!
//! Union-find data structure is common in compilers. So here is a simple
//! implementation of union-find data structure.

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;

use super::storage::{Arena, ArenaPtr, GenericPtr};
use crate::core::utils::Idx;
use crate::HashMap;

/// An entry in the union-find data structure
pub struct UnionFindEntry<T> {
    /// The parent of the entry.
    parent: T,
    /// The rank of the entry.
    ///
    /// We use [`u8`] to represent the rank. With union-by-rank method, a root
    /// with rank r has at least 2^r nodes, which is sufficient for most cases.
    ///
    /// The pinned root has rank 255, which is the maximum value of [`u8`].
    rank: u8,
}

/// A union-find data structure
///
/// This type is built for types that are cheap to copy. For those non-copyable
/// or expensive types, use [`ArenaUnionFind`] instead.
///
/// # Type Parameters
///
/// - `T`: The type of values representing disjoint sets.
///
/// # Examples
///
/// Here is an example of using `UnionFind`:
///
/// ```
/// use zuan::core::union_find::UnionFind;
///
/// let mut union_find = UnionFind::default();
///
/// union_find.insert(1);
/// union_find.insert(2);
///
/// // 1 and 2 are inserted as disjoint sets
/// assert_eq!(union_find.find(1), Some(1));
/// assert_eq!(union_find.find(2), Some(2));
///
/// union_find.union(1, 2); // union two sets
///
/// // 1 and 2 are merged into the same set
/// assert_eq!(union_find.find(1), Some(1));
/// assert_eq!(union_find.find(2), Some(1));
/// ```
///
/// It is recommended to use [`find_and_compress`](Self::find_and_compress)
/// when the union-find can be mutable.
pub struct UnionFind<T> {
    /// The entries indexed by the values.
    entries: HashMap<T, UnionFindEntry<T>>,
    /// The counter to record the number of broken pins (or conflict pins).
    broken_pin_counter: usize,
}

impl<T> Default for UnionFind<T> {
    fn default() -> Self {
        Self {
            entries: HashMap::new(),
            broken_pin_counter: 0,
        }
    }
}

impl<T: Copy + Eq + Hash> UnionFind<T> {
    /// Inserts a value as a new disjoint set.
    ///
    /// If the value already exists in the union-find this function does
    /// nothing.
    ///
    /// # Returns
    ///
    /// `true` if the value is inserted, `false` if the value already exists.
    pub fn insert(&mut self, value: T) -> bool {
        if self.entries.contains_key(&value) {
            return false;
        }
        self.entries.insert(
            value,
            UnionFindEntry {
                parent: value,
                rank: 0,
            },
        );
        true
    }

    /// Finds the representative (or the root) set of the value.
    ///
    /// This function does not compress the path, so it is not recommended to
    /// call this function multiple times. If the union-find can be mutable,
    /// [`find_and_compress`](Self::find_and_compress) is recommended.
    ///
    /// # Returns
    ///
    /// The representative set of the value. [`None`] if the value does not
    /// exist in the union-find.
    #[must_use = "`find` does not compress the path, its result should be used."]
    pub fn find(&self, value: T) -> Option<T> {
        let mut value = value;
        while let Some(entry) = self.entry(value) {
            if entry.parent == value {
                return Some(value);
            }
            value = entry.parent;
        }
        None
    }

    /// Finds the representative (or the root) set of the value and compresses
    /// the path.
    ///
    /// This function compresses the path, so it is recommended to call this
    /// function multiple times when the union-find can be mutated.
    ///
    /// If the union-find is not mutable, use [`find`](Self::find) instead.
    ///
    /// # Returns
    ///
    /// The representative set of the value. [`None`] if the value does not
    /// exist in the union-find.
    pub fn find_and_compress(&mut self, value: T) -> Option<T> {
        let entry = self.entries.get(&value)?;
        if entry.parent == value {
            Some(value)
        } else {
            let parent = entry.parent;
            let parent = self.find_and_compress(parent)?;
            self.entry_mut(value)
                .unwrap_or_else(|| unreachable!())
                .parent = parent;
            Some(parent)
        }
    }

    /// Pins the representative (or the root) set of the value so that all
    /// [`union`](Self::union) operations will merge other sets **into** this
    /// one.
    ///
    /// This will set the rank of the root to maximum, so when union is called,
    /// the root of this set will be the parent. An exception is when two sets
    /// are both pinned, one pin will be ignored and the rank remains the same.
    ///
    /// # Returns
    ///
    /// The representative set of the value. [`None`] if the value does not
    /// exist in the union-find.
    ///
    /// # Note
    ///
    /// This is adapted from Cranelift's implementation of union-find, which is
    /// specialized for e-graphs.
    pub fn pin(&mut self, value: T) -> Option<T> {
        let root = self.find_and_compress(value)?;
        self.entry_mut(root).unwrap_or_else(|| unreachable!()).rank = u8::MAX;
        Some(root)
    }

    /// Unions two sets that the given values belong to.
    ///
    /// This function does nothing if the two values belong to the same set.
    ///
    /// If the ranks of two sets are the same, the parent will be the first set.
    /// If two sets are all pinned, the first set will still be the parent, and
    /// the pinned-ness will be broken for the second set.
    ///
    /// To get the total number of broken pins, use
    /// [`broken_pins`](Self::broken_pins).
    ///
    /// # Parameters
    ///
    /// `a` and `b` are just two sets to merge, not necessarily the roots.
    ///
    /// # Returns
    ///
    /// The root of the merged set. [`None`] if any of the values does not exist
    /// in the union-find.
    ///
    /// # See also
    ///
    /// - [`pin`](Self::pin)
    pub fn union(&mut self, a: T, b: T) -> Option<T> {
        let mut a = self.find_and_compress(a)?;
        let mut b = self.find_and_compress(b)?;

        if a != b {
            let a_rank = self.entries.get(&a).unwrap_or_else(|| unreachable!()).rank;
            let b_rank = self.entries.get(&b).unwrap_or_else(|| unreachable!()).rank;

            match a_rank.cmp(&b_rank) {
                // keep `a` as the larger rank
                Ordering::Less => core::mem::swap(&mut a, &mut b),
                Ordering::Equal => {
                    // re-borrow to modify the broken pin counter in the closure
                    let entries = &mut self.entries;
                    // regard `a` as the parent
                    let entry = entries.get_mut(&a).unwrap_or_else(|| unreachable!());
                    // saturating add and update the broken pin counter if necessary
                    entry.rank = entry.rank.checked_add(1).unwrap_or_else(|| {
                        // Cranelift reports this by increasing a counter. Here we do the same
                        self.broken_pin_counter += 1;
                        u8::MAX
                    });
                }
                Ordering::Greater => {}
            }

            self.entry_mut(b).unwrap_or_else(|| unreachable!()).parent = a;
        }

        // `a` and `b` is swapped, and `a` is the assigned parent, so just return `a`
        Some(a)
    }

    /// Get the entry mutably, only allow for internal uses.
    fn entry_mut(&mut self, value: T) -> Option<&mut UnionFindEntry<T>> {
        self.entries.get_mut(&value)
    }

    /// Returns the entry of the value for low-level inspection.
    pub fn entry(&self, value: T) -> Option<&UnionFindEntry<T>> { self.entries.get(&value) }

    /// Returns the total number of broken pins in the [`union`](Self::union)
    /// operation.
    pub fn broken_pins(&self) -> usize { self.broken_pin_counter }
}

/// A union-find data structure that uses an arena to store data.
///
/// All inserted data are stored in the internal arena. If the data type is
/// small and cheap to copy, it is recommended to use [`UnionFind`] instead, for
/// it does not require an additional arena storage.
///
/// # Type Parameters
///
/// Any arenas can be used as the internal storage of the union-find, which
/// provides a more flexible way to manage the inserted values. For example, if
/// there is an arena that automatically makes the inserted values unique, this
/// union-find can be used to manage the sets of unique values.
///
/// - `T`: The type of the values stored in the union-find data structure.
/// - `P`: The type of the pointer used in the underlying arena, also indicates
///   the type of the arena. Default is [`GenericPtr`].
///
/// `P` must implement [`Eq`], [`Hash`] and [`ArenaPtr`] to be used as the key
/// in the internal union-find data structure. `P` is not required to be
/// copyable, but should be cheap to clone.
pub struct ArenaUnionFind<T, P = GenericPtr<T>>
where
    P: ArenaPtr<Data = T>,
{
    /// The internal arena.
    arena: P::Arena,
    /// The disjoint sets in the union-find data structure.
    union_find: UnionFind<Set<T, P>>,
}

impl<T, P> Default for ArenaUnionFind<T, P>
where
    P: ArenaPtr<Data = T>,
    P::Arena: Default,
{
    fn default() -> Self {
        Self {
            arena: P::Arena::default(),
            union_find: UnionFind::default(),
        }
    }
}

/// A handle to internal data in [`ArenaUnionFind`].
///
/// This is just a wrapper of the underlying pointer in the arena. It is used to
/// represent the data in the union-find data structure.
///
/// # Type Parameters
///
/// - `T`: The type of data stored in the union-find.
/// - `P`: The type of the pointer in the arena. Default is [`GenericPtr`].
///
/// `P` must implement [`Eq`], [`Hash`] and [`ArenaPtr`] to be used as the key
/// in the internal union-find data structure. `P` is not required to be
/// copyable, but should be cheap to clone.
pub struct Set<T, P = GenericPtr<T>> {
    /// The internal pointer to the data in the arena.
    ptr: P,
    _phantom: PhantomData<T>,
}

impl<T, P: Idx> Idx for Set<T, P> {
    fn index(self) -> usize { self.ptr.index() }
}

impl<T, P> Set<T, P> {
    fn from_ptr(ptr: P) -> Self {
        Self {
            ptr,
            _phantom: PhantomData,
        }
    }
}

impl<T, P: Clone> Clone for Set<T, P> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<T, P: Copy> Copy for Set<T, P> {}

impl<T, P: PartialEq> PartialEq for Set<T, P> {
    fn eq(&self, other: &Self) -> bool { self.ptr == other.ptr }
}

impl<T, P: Eq> Eq for Set<T, P> {}

impl<T, P: PartialOrd> PartialOrd for Set<T, P> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.ptr.partial_cmp(&other.ptr) }
}

impl<T, P: Ord> Ord for Set<T, P> {
    fn cmp(&self, other: &Self) -> Ordering { self.ptr.cmp(&other.ptr) }
}

impl<T, P: Hash> Hash for Set<T, P> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.ptr.hash(state) }
}

impl<T, P: fmt::Debug> fmt::Debug for Set<T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Set({:?})", self.ptr) }
}

impl<T, P: fmt::Display> fmt::Display for Set<T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Set({})", self.ptr) }
}

impl<T, P> ArenaPtr for Set<T, P>
where
    P: ArenaPtr<Data = T>,
{
    type Arena = ArenaUnionFind<T, P>;
    type Data = T;
}

impl<T, P> Arena<Set<T, P>> for ArenaUnionFind<T, P>
where
    P: ArenaPtr<Data = T>,
{
    /// Constructs a new set with a closure.
    ///
    /// This allows the underlying data to know its set.
    ///
    /// # Parameters
    ///
    /// - `f`: A function that takes a set and returns the data to be inserted.
    ///
    /// # Returns
    ///
    /// An allocated [Set] that represents the inserted data.
    fn alloc_with<F>(&mut self, f: F) -> Set<T, P>
    where
        F: FnOnce(Set<T, P>) -> T,
    {
        let set = Set::from_ptr(self.arena.alloc_with(|ptr| f(Set::from_ptr(ptr))));
        self.union_find.insert(set);
        set
    }

    /// De-allocation of a disjoint set never succeeds and always returns
    /// [`None`], because maintaining the union-find data structure when
    /// removing a set is complex and not recommended.
    fn try_dealloc(&mut self, _: Set<T, P>) -> Option<T> { None }

    /// Dereferences the set to get the internal data.
    ///
    /// This function does not find the root, but only dereferences the given
    /// set.
    fn try_deref(&self, set: Set<T, P>) -> Option<&T> { self.arena.try_deref(set.ptr) }

    /// Dereferences the set to get the mutable internal data.
    ///
    /// This function does not find the root, but only dereferences the given
    /// set.
    fn try_deref_mut(&mut self, set: Set<T, P>) -> Option<&mut T> {
        self.arena.try_deref_mut(set.ptr)
    }
}

impl<T> ArenaUnionFind<T> {
    /// Creates a new [ArenaUnionFind] with default settings.
    pub fn new() -> Self { Self::default() }
}

impl<T, P> ArenaUnionFind<T, P>
where
    P: ArenaPtr<Data = T> + Eq + Hash + Clone,
{
    /// Inserts data with a closure and make it a set.
    ///
    /// This allows the underlying data to know its set.
    ///
    /// This is just a wrapper of [`alloc_with`](Self::alloc_with), which
    /// automatically inserts the set into the union-find data structure to make
    /// all allocated sets valid.
    ///
    /// # Parameters
    ///
    /// - `f`: A closure that takes the allocated set and returns the
    ///   constructed data.
    ///
    /// # Returns
    ///
    /// The set that represents the inserted data.
    pub fn insert_with<F>(&mut self, f: F) -> Set<T, P>
    where
        F: FnOnce(Set<T, P>) -> <Set<T, P> as ArenaPtr>::Data,
    {
        self.alloc_with(f)
    }

    /// Inserts constructed data and make it a set.
    ///
    /// This is just a wrapper of [`alloc`](Self::alloc).
    ///
    /// # Returns
    ///
    /// The set that represents the inserted data.
    ///
    /// # See also
    ///
    /// - [`ArenaUnionFind::insert_with`]
    pub fn insert(&mut self, value: T) -> Set<T, P> { self.insert_with(|_| value) }

    /// Finds the root of the given set.
    ///
    /// This function does not compress the path, so it is not recommended to
    /// call this function multiple times. If the union-find can be mutable,
    /// [`find_and_compress`](Self::find_and_compress) is recommended.
    ///
    /// # Panics
    ///
    /// Panics if the set does not exist in the union-find.
    ///
    /// The [`Set`] should always be constructed by the arena, so it should
    /// always be valid and should not panic.
    ///
    /// # See also
    ///
    /// - [`UnionFind::find`]
    #[must_use = "`find` does not compress the path, its result should be used."]
    pub fn find(&self, set: Set<T, P>) -> Set<T, P> { self.union_find.find(set).unwrap() }

    /// Finds the root of the set and compresses the path.
    ///
    /// If the union-find is not mutable, use [`find`](Self::find) instead.
    ///
    /// # Panics
    ///
    /// Panics if the set does not exist in the union-find.
    ///
    /// The [`Set`] should always be constructed by the arena, so it should
    /// always be valid.
    ///
    /// # See also
    ///
    /// - [`UnionFind::find_and_compress`]
    pub fn find_and_compress(&mut self, set: Set<T, P>) -> Set<T, P> {
        self.union_find.find_and_compress(set).unwrap()
    }

    /// Pins the representative of the set.
    ///
    /// # Returns
    ///
    /// The root of the set.
    ///
    /// # Panics
    ///
    /// Panics if the set does not exist in the union-find.
    ///
    /// The set can only be constructed by the arena, so it should always be
    /// valid.
    ///
    /// # See also
    ///
    /// - [`UnionFind::pin`]
    pub fn pin(&mut self, set: Set<T, P>) -> Set<T, P> { self.union_find.pin(set).unwrap() }

    /// Unions two sets.
    ///
    /// This function does nothing if the two sets share the same root.
    ///
    /// # Returns
    ///
    /// The root of the merged set. [`None`] if any of the sets does not exist
    /// in the union-find.
    ///
    /// # Panics
    ///
    /// Panics if any of the sets does not exist in the union-find.
    ///
    /// The set can only be constructed by the arena, so it should always be
    /// valid.
    ///
    /// # See also
    ///
    /// - [`UnionFind::union`]
    pub fn union(&mut self, a: Set<T, P>, b: Set<T, P>) -> Set<T, P> {
        self.union_find.union(a, b).unwrap()
    }

    /// Returns the total number of broken pins in the [`union`](Self::union)
    /// operation.
    pub fn broken_pins(&self) -> usize { self.union_find.broken_pins() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::storage::{Arena, GenericArena};

    #[test]
    fn test_union_find_arena_ptr() {
        let arena = &mut GenericArena::default();

        let mut union_find = UnionFind::default();

        let a = arena.alloc(1);
        let b = arena.alloc(2);
        let c = arena.alloc(3);
        let d = arena.alloc(4);

        assert!(union_find.insert(a));
        assert!(union_find.insert(b));
        assert!(union_find.insert(c));
        assert!(union_find.insert(d));

        assert!(!union_find.insert(a));

        assert_eq!(union_find.find(a), Some(a));
        assert_eq!(union_find.find(b), Some(b));
        assert_eq!(union_find.find(c), Some(c));
        assert_eq!(union_find.find(d), Some(d));

        assert_eq!(union_find.union(a, b), Some(a));

        assert_eq!(union_find.find(a), Some(a));
        assert_eq!(union_find.find(b), Some(a));
        assert_eq!(union_find.find(c), Some(c));
        assert_eq!(union_find.find(d), Some(d));

        assert_eq!(union_find.union(c, d), Some(c));

        assert_eq!(union_find.find(a), Some(a));
        assert_eq!(union_find.find(b), Some(a));
        assert_eq!(union_find.find(c), Some(c));
        assert_eq!(union_find.find(d), Some(c));

        assert_eq!(union_find.union(b, c), Some(a));

        assert_eq!(union_find.find(a), Some(a));
        assert_eq!(union_find.find(b), Some(a));
        assert_eq!(union_find.find(c), Some(a));
        assert_eq!(union_find.find(d), Some(a));
    }

    #[test]
    fn test_union_find_int() {
        let mut union_find = UnionFind::default();

        union_find.insert(1);
        union_find.insert(2);
        union_find.insert(3);
        union_find.insert(4);

        assert_eq!(union_find.find(1), Some(1));
        assert_eq!(union_find.find(2), Some(2));
        assert_eq!(union_find.find(3), Some(3));
        assert_eq!(union_find.find(4), Some(4));
        assert_eq!(union_find.find(5), None);

        assert_eq!(union_find.union(1, 2), Some(1));

        assert_eq!(union_find.find(1), Some(1));
        assert_eq!(union_find.find(2), Some(1));
        assert_eq!(union_find.find(3), Some(3));
        assert_eq!(union_find.find(4), Some(4));
        assert_eq!(union_find.find(0), None);

        assert_eq!(union_find.union(3, 4), Some(3));

        assert_eq!(union_find.find(1), Some(1));
        assert_eq!(union_find.find(2), Some(1));
        assert_eq!(union_find.find(3), Some(3));
        assert_eq!(union_find.find(4), Some(3));
        assert_eq!(union_find.find(7), None);

        assert_eq!(union_find.union(2, 3), Some(1));

        assert_eq!(union_find.find(1), Some(1));
        assert_eq!(union_find.find(2), Some(1));
        assert_eq!(union_find.find(3), Some(1));
        assert_eq!(union_find.find(4), Some(1));
        assert_eq!(union_find.find(6), None);
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Point {
        x: i32,
        y: i32,
    }

    #[test]
    fn test_arena_union_find() {
        let mut union_find = ArenaUnionFind::new();

        let a = union_find.insert(Point { x: 1, y: 2 });
        let b = union_find.insert(Point { x: 3, y: 4 });
        let c = union_find.insert(Point { x: 5, y: 6 });
        let d = union_find.insert(Point { x: 7, y: 8 });

        assert_eq!(union_find.find(a), a);
        assert_eq!(union_find.find(b), b);
        assert_eq!(union_find.find(c), c);
        assert_eq!(union_find.find(d), d);

        assert_eq!(union_find.union(a, b), a);

        assert_eq!(union_find.find(a), a);
        assert_eq!(union_find.find(b), a);
        assert_eq!(union_find.find(c), c);
        assert_eq!(union_find.find(d), d);

        assert_eq!(union_find.union(c, d), c);

        assert_eq!(union_find.find(a), a);
        assert_eq!(union_find.find(b), a);
        assert_eq!(union_find.find(c), c);
        assert_eq!(union_find.find(d), c);

        assert_eq!(union_find.find(c).try_deref(&union_find).unwrap().x, 5);
        assert_eq!(union_find.find(d).try_deref(&union_find).unwrap().y, 6);

        assert_eq!(union_find.union(b, c), a);

        assert_eq!(union_find.find(a), a);
        assert_eq!(union_find.find(b), a);
        assert_eq!(union_find.find(c), a);
        assert_eq!(union_find.find(d), a);

        assert_eq!(union_find.find(c).try_deref(&union_find).unwrap().x, 1);
        assert_eq!(union_find.find(d).try_deref(&union_find).unwrap().y, 2);
    }

    #[test]
    fn test_find_and_compress() {
        let mut union_find = UnionFind::default();

        union_find.insert(1);
        union_find.insert(2);
        union_find.insert(3);
        union_find.insert(4);

        assert_eq!(union_find.union(1, 2), Some(1));
        assert_eq!(union_find.union(3, 4), Some(3));

        assert_eq!(union_find.union(1, 3), Some(1)); // same rank, 1 <- 3

        assert_eq!(union_find.entry(2).unwrap().parent, 1);
        assert_eq!(union_find.entry(3).unwrap().parent, 1);
        assert_eq!(union_find.entry(1).unwrap().parent, 1);
        // can be compressed
        assert_eq!(union_find.entry(4).unwrap().parent, 3);

        assert_eq!(union_find.find(4), Some(1));
        assert_eq!(union_find.entry(4).unwrap().parent, 3);

        assert_eq!(union_find.find_and_compress(4), Some(1));
        assert_eq!(union_find.entry(4).unwrap().parent, 1);
    }

    #[test]
    fn test_union_find_pinned() {
        let mut union_find = UnionFind::default();

        union_find.insert(1);
        union_find.insert(2);
        union_find.insert(3);
        union_find.insert(4);

        assert_eq!(union_find.find(1), Some(1));
        assert_eq!(union_find.find(2), Some(2));
        assert_eq!(union_find.find(3), Some(3));
        assert_eq!(union_find.find(4), Some(4));
        assert_eq!(union_find.find(5), None);

        union_find.pin(2);
        assert_eq!(union_find.union(1, 2), Some(2));

        assert_eq!(union_find.find(1), Some(2));
        assert_eq!(union_find.find(2), Some(2));
        assert_eq!(union_find.find(3), Some(3));
        assert_eq!(union_find.find(4), Some(4));
        assert_eq!(union_find.find(0), None);

        union_find.pin(4);
        assert_eq!(union_find.union(3, 4), Some(4));

        assert_eq!(union_find.find(1), Some(2));
        assert_eq!(union_find.find(2), Some(2));
        assert_eq!(union_find.find(3), Some(4));
        assert_eq!(union_find.find(4), Some(4));
        assert_eq!(union_find.find(7), None);

        // both pinned, should be the first one
        assert_eq!(union_find.union(2, 3), Some(2));

        assert_eq!(union_find.find(1), Some(2));
        assert_eq!(union_find.find(2), Some(2));
        assert_eq!(union_find.find(3), Some(2));
        assert_eq!(union_find.find(4), Some(2));
        assert_eq!(union_find.find(6), None);
    }

    #[test]
    fn test_arena_union_find_dealloc() {
        let mut union_find = ArenaUnionFind::new();

        let a = union_find.insert(Point { x: 1, y: 2 });
        let b = union_find.insert(Point { x: 3, y: 4 });

        union_find.union(a, b);

        assert_eq!(union_find.try_dealloc(a), None);
    }

    #[test]
    fn test_broken_pins() {
        let mut union_find = UnionFind::default();

        union_find.insert(1);
        union_find.insert(2);
        union_find.insert(3);
        union_find.insert(4);

        union_find.union(1, 2);
        union_find.union(3, 4);

        assert_eq!(union_find.broken_pins(), 0);

        union_find.pin(2); // rank[1] <- u8::MAX
        union_find.pin(4); // rank[3] <- u8::MAX

        // same rank, 1 <- 3, both pinned
        assert_eq!(union_find.union(1, 3), Some(1));

        assert_eq!(union_find.broken_pins(), 1);
    }
}
