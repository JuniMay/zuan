//! Storage Infrastructure
//!
//! This module provides [`Arena`] and [`ArenaPtr`] as storage infrastructure.
//! One can utilize [`GenericArena`] and [`GenericPtr`] as the basic arena and
//! pointer to build complex storage internals.
//!
//! The arenas can be used to store some expensive-to-copy data or non-copyable
//! data. The arena pointers are handles to the data stored in the arena.
//!
//! Arenas can be used for linked lists, graphs, and union-find data structures.
//! But in some implementations of those data structures, the underlying storage
//! (or context) is not restricted, which tends to be more flexible.
//!
//! # See also
//!
//! - [Linked List](crate::core::linked_list)
//! - [Union-Find](crate::core::union_find)

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::{fmt, mem};

use crate::core::utils::Idx;

/// A trait for indexing into an arena.
pub trait ArenaPtr: Copy + Eq + Hash {
    /// The arena type, which should support the pointer type.
    type Arena: Arena<Self>;

    /// The internal data.
    type Data;

    /// Try to dereference the pointer with an arena.
    ///
    /// # Returns
    ///
    /// - `Some(&Self::Data)`: A reference to the data in the arena.
    /// - `None`: The pointer is invalid.
    fn try_deref(self, arena: &Self::Arena) -> Option<&Self::Data> { arena.try_deref(self) }

    /// Try to mutably dereference the pointer with an arena.
    ///
    /// # Returns
    ///
    /// - `Some(&mut Self::Data)`: A mutable reference to the data in the arena.
    /// - `None`: The pointer is invalid.
    fn try_deref_mut(self, arena: &mut Self::Arena) -> Option<&mut Self::Data> {
        arena.try_deref_mut(self)
    }
}

/// A trait for an arena that can store data and allocate pointers.
///
/// # Type Parameters
///
/// - `Ptr`: The pointer type that is supported by the arena. The data type is
///   inferred from the pointer type by using [`ArenaPtr::Data`].
pub trait Arena<Ptr>
where
    Ptr: ArenaPtr<Arena = Self>,
{
    /// Construct data with the allocated pointer and store it into the arena.
    ///
    /// This allows the stored data to know its own pointer.
    ///
    /// # Parameters
    ///
    /// - `f`: A function that takes the allocated pointer and returns the
    ///   constructed data.
    ///
    /// # Returns
    ///
    /// The allocated pointer to the stored data.
    fn alloc_with<F>(&mut self, f: F) -> Ptr
    where
        F: FnOnce(Ptr) -> Ptr::Data;

    /// Store data into the arena and return the allocated pointer.
    fn alloc(&mut self, data: Ptr::Data) -> Ptr { self.alloc_with(|_| data) }

    /// Deallocate the data of the pointer from the arena.
    ///
    /// # Returns
    ///
    /// - `Some(Ptr::Data)`: The data of the deallocated pointer.
    /// - `None`: The pointer is invalid.
    fn try_dealloc(&mut self, ptr: Ptr) -> Option<Ptr::Data>;

    /// Try to dereference a pointer.
    ///
    /// # Returns
    ///
    /// - `Some(&Ptr::Data)`: A reference to the data in the arena.
    /// - `None`: The pointer is invalid.
    fn try_deref(&self, ptr: Ptr) -> Option<&Ptr::Data>;

    /// Try to mutably dereference a pointer.
    ///
    /// # Returns
    ///
    /// - `Some(&mut Ptr::Data)`: A mutable reference to the data in the arena.
    /// - `None`: The pointer is invalid.
    fn try_deref_mut(&mut self, ptr: Ptr) -> Option<&mut Ptr::Data>;
}

/// A generic arena pointer.
///
/// The pointer can only be allocated by [`GenericArena`]. One should not create
/// a pointer manually.
///
/// The internal of this pointer is a raw index into the arena. It is not
/// generational, so the user should be careful after re-allocation.
///
/// The pointer implements [`Ord`] to allow sorting. The order is based on the
/// raw index, i.e., the position of the data in the arena.
///
/// # Type Parameters
///
/// - `Data`: The type of the stored data, which is the same as the data type in
///   the arena.
pub struct GenericPtr<Data> {
    /// The raw index of the pointer.
    index: usize,
    _phantom: PhantomData<Data>,
}

impl<Data> GenericPtr<Data> {
    fn from_index(index: usize) -> Self {
        Self {
            index,
            _phantom: PhantomData,
        }
    }
}

impl<Data> Idx for GenericPtr<Data> {
    fn index(self) -> usize { self.index }
}

impl<Data> Clone for GenericPtr<Data> {
    fn clone(&self) -> Self { *self }
}

impl<Data> Copy for GenericPtr<Data> {}

impl<Data> Hash for GenericPtr<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.index.hash(state) }
}

impl<Data> PartialEq for GenericPtr<Data> {
    fn eq(&self, other: &Self) -> bool { self.index == other.index }
}

impl<Data> Eq for GenericPtr<Data> {}

impl<Data> PartialOrd for GenericPtr<Data> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl<Data> Ord for GenericPtr<Data> {
    fn cmp(&self, other: &Self) -> Ordering { self.index.cmp(&other.index) }
}

impl<Data> fmt::Debug for GenericPtr<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "*{}", self.index) }
}

impl<Data> fmt::Display for GenericPtr<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "*{}", self.index) }
}

impl<Data> fmt::Pointer for GenericPtr<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "*{:x}", self.index) }
}

impl<Data> fmt::LowerHex for GenericPtr<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "*{:x}", self.index) }
}

impl<Data> fmt::UpperHex for GenericPtr<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "*{:X}", self.index) }
}

/// An entry in a generic arena.
pub enum GenericEntry<Data> {
    /// The entry is vacant.
    ///
    /// The free list is not ordered by its index, but by the order of
    /// de-allocation, the last deallocated entry will be the first entry in
    /// the free list.
    Vacant {
        /// The index of the next vacant entry.
        next: Option<usize>,
    },
    /// The entry is occupied.
    Occupied(Data),
}

/// A generic arena.
///
/// # Type Parameters
///
/// - `Data`: The type of the stored data. All allocated pointers will have this
///   as the data type.
///
/// # Examples
///
/// ```
/// use zuan::core::storage::{GenericArena, Arena, ArenaPtr};
///
/// let mut arena = GenericArena::default();
///
/// let one = arena.alloc(1); // allocate a pointer with data 1
/// let two = arena.alloc(2); // allocate a pointer with data 2
///
/// assert_ne!(one, two); // allocated pointers are different
///
/// // dereference the pointers to get the data
/// assert_eq!(one.try_deref(&arena), Some(&1));
/// assert_eq!(two.try_deref(&arena), Some(&2));
///
/// // use `deref_mut` to modify the data
/// *two.try_deref_mut(&mut arena).unwrap() = 3;
/// assert_eq!(two.try_deref(&arena), Some(&3)); // the data is modified
/// ```
pub struct GenericArena<Data> {
    /// The entries in the arena.
    ///
    /// An entry is not valid if it is [`GenericEntry::Vacant`]. Otherwise, it
    /// should store the data.
    entries: Vec<GenericEntry<Data>>,
    /// The head of the free list.
    ///
    /// This is the index of the first vacant entry, also the last deallocated
    /// entry.
    free_head: Option<usize>,
}

impl<Data> Default for GenericArena<Data> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            free_head: None,
        }
    }
}

impl<Data> GenericArena<Data> {
    /// Reserve additional capacity.
    pub fn reserve(&mut self, additional: usize) { self.entries.reserve(additional) }

    /// Create a new arena with a specific capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
            free_head: None,
        }
    }

    /// Iterate over the stored data.
    pub fn iter(&self) -> impl Iterator<Item = &Data> {
        self.entries.iter().filter_map(|entry| match entry {
            GenericEntry::Occupied(value) => Some(value),
            GenericEntry::Vacant { .. } => None,
        })
    }

    /// Iterate mutably over the stored data.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Data> {
        self.entries.iter_mut().filter_map(|entry| match entry {
            GenericEntry::Occupied(value) => Some(value),
            GenericEntry::Vacant { .. } => None,
        })
    }
}

impl<Data> ArenaPtr for GenericPtr<Data> {
    type Arena = GenericArena<Data>;
    type Data = Data;
}

impl<Data> Arena<GenericPtr<Data>> for GenericArena<Data> {
    fn alloc_with<F>(&mut self, f: F) -> GenericPtr<Data>
    where
        F: FnOnce(GenericPtr<Data>) -> Data,
    {
        match self.free_head.take() {
            Some(index) => {
                let entry = &mut self.entries[index];
                self.free_head = match entry {
                    // the vacant will be taken, so the next will be the new `free_head`
                    GenericEntry::Vacant { next } => *next,
                    // we have a `free_head`, this entry should be vacant
                    GenericEntry::Occupied(_) => unreachable!(),
                };
                let ptr = GenericPtr::from_index(index);
                *entry = GenericEntry::Occupied(f(ptr)); // set the entry to occupied
                ptr
            }
            None => {
                // we have no `free_head`, so we need to push a new entry
                let index = self.entries.len();
                let ptr = GenericPtr::from_index(index);
                self.entries.push(GenericEntry::Occupied(f(ptr)));
                ptr
            }
        }
    }

    fn try_dealloc(&mut self, ptr: GenericPtr<Data>) -> Option<Data> {
        let index = ptr.index();
        if index >= self.entries.len() {
            return None;
        }
        let old_entry = mem::replace(
            &mut self.entries[index],
            GenericEntry::Vacant {
                next: self.free_head,
            },
        );
        self.free_head = Some(index);
        match old_entry {
            GenericEntry::Vacant { .. } => None,
            GenericEntry::Occupied(data) => Some(data),
        }
    }

    fn try_deref(&self, ptr: GenericPtr<Data>) -> Option<&Data> {
        match self.entries.get(ptr.index())? {
            GenericEntry::Occupied(value) => Some(value),
            GenericEntry::Vacant { .. } => None,
        }
    }

    fn try_deref_mut(&mut self, ptr: GenericPtr<Data>) -> Option<&mut Data> {
        match self.entries.get_mut(ptr.index())? {
            GenericEntry::Occupied(value) => Some(value),
            GenericEntry::Vacant { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generic_arena() {
        let mut arena = GenericArena::default();
        let ptr1 = arena.alloc(1);
        let ptr2 = arena.alloc(2);
        let ptr3 = arena.alloc(3);
        assert_eq!(ptr1.try_deref(&arena), Some(&1));
        assert_eq!(ptr2.try_deref(&arena), Some(&2));
        assert_eq!(ptr3.try_deref(&arena), Some(&3));
        assert_eq!(arena.iter().collect::<Vec<_>>(), vec![&1, &2, &3]);
        assert_eq!(
            arena.iter_mut().collect::<Vec<_>>(),
            vec![&mut 1, &mut 2, &mut 3]
        );
        assert_eq!(arena.try_dealloc(ptr2), Some(2));
        assert_eq!(arena.iter().collect::<Vec<_>>(), vec![&1, &3]);
        assert_eq!(arena.iter_mut().collect::<Vec<_>>(), vec![&mut 1, &mut 3]);
        let ptr4 = arena.alloc(4);
        // not a generational arena, so ptr4 is the same as ptr2
        assert_eq!(ptr2, ptr4);
        assert_eq!(ptr4.try_deref(&arena), Some(&4));
        assert_eq!(arena.iter().collect::<Vec<_>>(), vec![&1, &4, &3]);
        assert_eq!(
            arena.iter_mut().collect::<Vec<_>>(),
            vec![&mut 1, &mut 4, &mut 3]
        );
    }

    #[test]
    fn test_generic_arena_double_free() {
        let mut arena = GenericArena::default();
        let ptr1 = arena.alloc(1);
        assert_eq!(arena.try_dealloc(ptr1), Some(1));
        assert_eq!(arena.try_dealloc(ptr1), None); // double free
    }

    #[test]
    fn test_generic_arena_invalid_index() {
        let mut arena = GenericArena::default();
        let ptr1 = arena.alloc(1);
        let mut ptr2 = ptr1;
        ptr2.index = 1; // should not happen in normal usage
        assert_eq!(arena.try_dealloc(ptr2), None);
    }

    #[test]
    fn test_generic_arena_deref() {
        let mut arena = GenericArena::default();
        let ptr1 = arena.alloc(1);
        let ptr2 = arena.alloc(2);
        let ptr3 = arena.alloc(3);
        assert_eq!(ptr1.try_deref(&arena), Some(&1));
        assert_eq!(ptr2.try_deref(&arena), Some(&2));
        assert_eq!(ptr3.try_deref(&arena), Some(&3));
        assert_eq!(ptr1.try_deref_mut(&mut arena), Some(&mut 1));
        assert_eq!(ptr2.try_deref_mut(&mut arena), Some(&mut 2));
        assert_eq!(ptr3.try_deref_mut(&mut arena), Some(&mut 3));
        assert_eq!(arena.try_dealloc(ptr2), Some(2));
        assert_eq!(ptr1.try_deref(&arena), Some(&1));
        assert_eq!(ptr2.try_deref(&arena), None);
        assert_eq!(ptr3.try_deref(&arena), Some(&3));
        assert_eq!(ptr1.try_deref_mut(&mut arena), Some(&mut 1));
        assert_eq!(ptr2.try_deref_mut(&mut arena), None);
        assert_eq!(ptr3.try_deref_mut(&mut arena), Some(&mut 3));
    }

    #[test]
    fn test_generic_arena_invalid_deref() {
        let mut arena = GenericArena::default();
        let ptr1 = arena.alloc(1);
        assert_eq!(arena.try_dealloc(ptr1), Some(1));
        assert_eq!(ptr1.try_deref(&arena), None); // invalid deref
    }
}
