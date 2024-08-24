//! Utility types and traits.

use core::fmt;
use core::hash::Hash;

/// A trait represents a lightweight index.
///
/// The internal can be arbitrary, but it should be able to convert to a raw and
/// *unique* [`usize`] index.
///
/// This trait has no nothing to do with [`ArenaPtr`](super::storage::ArenaPtr),
/// but a more general abstraction for types that can be used as an index.
pub trait Idx: Copy + Ord + Hash {
    /// Get the raw [`usize`] from the index.
    fn index(self) -> usize;
}

impl Idx for usize {
    fn index(self) -> usize { self }
}

/// Represents a type with reserved value.
pub trait Reserved {
    /// Create an invalid/reserved value.
    fn reserved() -> Self;

    /// Check if the value is reserved.
    fn is_reserved(&self) -> bool;
}

/// A wrapper of [`Reserved`] types.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackedOption<T: Reserved>(T);

impl<T: Reserved> Default for PackedOption<T> {
    fn default() -> Self { Self(T::reserved()) }
}

impl<T: Reserved> PackedOption<T> {
    /// Create a new non-reserved value.
    ///
    /// # Panics
    ///
    /// Panics if the value is reserved.
    pub fn some(value: T) -> Self {
        assert!(
            !value.is_reserved(),
            "called `PackedOption::some()` with a reserved value"
        );
        Self(value)
    }

    /// Create a new reserved value.
    pub fn none() -> Self { Self::default() }

    /// Returns `true` if the option is a reserved value.
    #[must_use]
    pub fn is_none(&self) -> bool { self.0.is_reserved() }

    /// Returns `true` if the option is not a reserved value.
    #[must_use]
    pub fn is_some(&self) -> bool { !self.is_none() }

    /// Expand the packed option into an option.
    #[must_use]
    pub fn unpack(self) -> Option<T> {
        if self.0.is_reserved() {
            None
        } else {
            Some(self.0)
        }
    }

    /// Consume the packed value and return the contained value.
    ///
    /// # Panics
    ///
    /// Panics if the value is reserved.
    pub fn unwrap(self) -> T {
        if self.0.is_reserved() {
            panic!("called `PackedOption::unwrap()` on a `None` value");
        }
        self.0
    }

    /// Unwrap or return the provided default value.
    pub fn unwrap_or(self, default: T) -> T {
        if self.0.is_reserved() {
            default
        } else {
            self.0
        }
    }

    /// Unwrap or execute the provided closure.
    pub fn unwrap_or_else(self, f: impl FnOnce() -> T) -> T {
        if self.0.is_reserved() {
            f()
        } else {
            self.0
        }
    }

    /// Consume the packed value and return the contained value.
    ///
    /// # Panics
    ///
    /// Panics with a custom message if the value is reserved with the provided
    /// message.
    pub fn expect(self, msg: &str) -> T {
        if self.0.is_reserved() {
            panic!("{}", msg);
        }
        self.0
    }
}

impl<T> fmt::Debug for PackedOption<T>
where
    T: Reserved + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_some() {
            write!(f, "Some({:?})", self.0)
        } else {
            write!(f, "None")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
    struct TestReserved(u32);

    impl Reserved for TestReserved {
        fn reserved() -> Self { Self(u32::MAX) }

        fn is_reserved(&self) -> bool { self.0 == u32::MAX }
    }

    #[test]
    fn test_packed_option() {
        let some = PackedOption::some(TestReserved(42));
        assert!(some.is_some());
        assert_eq!(some.unpack(), Some(TestReserved(42)));
        assert_eq!(some.unwrap(), TestReserved(42));
        assert_eq!(some.expect("expect"), TestReserved(42));

        let none = PackedOption::<TestReserved>::none();
        assert!(none.is_none());
        assert_eq!(none.unpack(), None);
    }

    #[test]
    fn test_packed_option_dbg() {
        let some = PackedOption::some(TestReserved(42));
        assert_eq!(format!("{:?}", some), "Some(TestReserved(42))");

        let none = PackedOption::<TestReserved>::none();
        assert_eq!(format!("{:?}", none), "None");
    }

    #[test]
    #[should_panic]
    fn test_packed_option_unwrap() {
        let none = PackedOption::<TestReserved>::none();
        none.unwrap();
    }
}
