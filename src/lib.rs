//! # Zuan Compiler Infrastructure

#![deny(missing_docs)]
#![no_std]
#![forbid(unsafe_code)]

#[allow(unused_imports)]
#[macro_use]
extern crate alloc;
#[cfg(feature = "std")]
#[macro_use]
extern crate std;

#[cfg(feature = "std")]
use std::collections::{HashMap, HashSet};

#[cfg(not(feature = "std"))]
use hashbrown::{HashMap, HashSet};

pub mod core;
