//! The [`bit_flags!`](crate::bit_flags) macro. It lives at the root of the crate.

/// Defines a set of flags: a small integer where every bit stands for one thing, with the
/// operators and methods that go with it.
///
/// ```
/// use anythingy::bit_flags;
///
/// bit_flags! {
///     /// What a buffer is used for.
///     #[derive(PartialOrd, Ord)]    // optional: any attributes go on the struct
///     pub struct BufferKind: u8 {
///         /// Vertex data.
///         const VERTEX = 1 << 0;
///         /// Indices into vertex data.
///         const INDEX = 1 << 1;
///         /// A flag may combine others, through `bits()` (a constant function).
///         const GEOMETRY = Self::VERTEX.bits() | Self::INDEX.bits();
///     }
/// }
///
/// let mut kind = BufferKind::VERTEX | BufferKind::INDEX;
/// assert!(kind.contains(BufferKind::VERTEX));
/// // Listed by what was declared first: `VERTEX` and `INDEX` come before `GEOMETRY`.
/// assert_eq!(format!("{kind:?}"), "VERTEX | INDEX");
///
/// kind -= BufferKind::INDEX;
/// assert_eq!(kind, BufferKind::VERTEX);
/// assert_eq!(!kind, BufferKind::INDEX);
/// ```
///
/// What is made:
/// - A `Copy` struct around the integer type, with `Clone`, `PartialEq`, `Eq`, `Hash` and
///   `Default` (no flag set), and the other derives and doc comments that are given as
///   attributes. (`Default` is implemented by the macro, so it is not derived.)
/// - One associated constant for each flag. A flag with the value 0 is allowed (a name for
///   "none"): it is contained in everything, so it is never listed in the other flags' output.
/// - Constant functions: `empty`, `all`, `bits`, `from_bits` (`None` if a bit is not a flag),
///   `from_bits_truncate`, `is_empty`, `is_all`, `contains`, `intersects`, `union`,
///   `intersection`, `difference`, `symmetric_difference`, `complement`.
/// - `insert`, `remove`, `toggle` and `set` to change a value in place.
/// - `iter` and `iter_names`: the flags that are set, in the order they were declared.
/// - The operators `|`, `&`, `^`, `-` (remove), `!` (the flags that are not set, of the declared
///   ones) and their assignment forms, and `FromIterator` and `Extend`.
/// - `Debug` (the names, joined by ` | `, in declaration order; see below), `Binary`, `Octal`,
///   `LowerHex` and `UpperHex` (of the bits).
///
/// Listing goes through the flags in the order they were declared, and takes a flag when all its
/// bits are set and none was taken by an earlier one. So a combination that is declared before
/// its parts is listed instead of them, and one that is declared after them is never listed.
///
/// The integer type must be an unsigned one (`u8` to `u128`, `usize`). Nothing checks that two
/// flags use different bits: a flag that is a combination of others is fine, and so is a
/// mistake.
///
/// It works without `std`.
#[macro_export]
macro_rules! bit_flags {
    (
        $(#[$struct_meta:meta])*
        $vis:vis struct $name:ident: $ty:ty {
            $(
                $(#[$flag_meta:meta])*
                const $flag:ident = $value:expr;
            )*
        }
    ) => {
        $(#[$struct_meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        $vis struct $name($ty);

        #[allow(dead_code, reason = "a set of flags offers all of its functions, used or not")]
        impl $name {
            $(
                $(#[$flag_meta])*
                pub const $flag: Self = Self($value);
            )*

            /// Every flag that is declared, with its name, in the order of declaration.
            const FLAGS: &'static [(&'static str, $ty)] = &[
                $( (stringify!($flag), $value), )*
            ];

            /// The bits of all the flags together.
            const ALL_BITS: $ty = 0 $( | $value )*;

            /// No flag set.
            #[must_use]
            pub const fn empty() -> Self {
                Self(0)
            }

            /// All the flags set.
            #[must_use]
            pub const fn all() -> Self {
                Self(Self::ALL_BITS)
            }

            /// The bits, as the integer they are stored in.
            #[must_use]
            pub const fn bits(self) -> $ty {
                self.0
            }

            /// The flags for `bits`, or `None` if a bit is set that no flag has.
            #[must_use]
            pub const fn from_bits(bits: $ty) -> Option<Self> {
                if bits & !Self::ALL_BITS == 0 {
                    Some(Self(bits))
                } else {
                    None
                }
            }

            /// The flags for `bits`, leaving out the bits that no flag has.
            #[must_use]
            pub const fn from_bits_truncate(bits: $ty) -> Self {
                Self(bits & Self::ALL_BITS)
            }

            /// Whether no flag is set.
            #[must_use]
            pub const fn is_empty(self) -> bool {
                self.0 == 0
            }

            /// Whether every flag is set.
            #[must_use]
            pub const fn is_all(self) -> bool {
                self.0 == Self::ALL_BITS
            }

            /// Whether every flag in `other` is also in `self`. (Always true for no flag.)
            #[must_use]
            pub const fn contains(self, other: Self) -> bool {
                self.0 & other.0 == other.0
            }

            /// Whether at least one flag is in both.
            #[must_use]
            pub const fn intersects(self, other: Self) -> bool {
                self.0 & other.0 != 0
            }

            /// The flags that are in `self` or `other`.
            #[must_use]
            pub const fn union(self, other: Self) -> Self {
                Self(self.0 | other.0)
            }

            /// The flags that are in both.
            #[must_use]
            pub const fn intersection(self, other: Self) -> Self {
                Self(self.0 & other.0)
            }

            /// The flags of `self` that are not in `other`.
            #[must_use]
            pub const fn difference(self, other: Self) -> Self {
                Self(self.0 & !other.0)
            }

            /// The flags that are in one of them, but not in both.
            #[must_use]
            pub const fn symmetric_difference(self, other: Self) -> Self {
                Self(self.0 ^ other.0)
            }

            /// The declared flags that are not set.
            #[must_use]
            pub const fn complement(self) -> Self {
                Self(!self.0 & Self::ALL_BITS)
            }

            /// Sets the flags of `other`.
            pub const fn insert(&mut self, other: Self) {
                self.0 |= other.0;
            }

            /// Clears the flags of `other`.
            pub const fn remove(&mut self, other: Self) {
                self.0 &= !other.0;
            }

            /// Flips the flags of `other`.
            pub const fn toggle(&mut self, other: Self) {
                self.0 ^= other.0;
            }

            /// Sets the flags of `other` if `value` is true, and clears them if it is not.
            pub const fn set(&mut self, other: Self, value: bool) {
                if value {
                    self.insert(other);
                } else {
                    self.remove(other);
                }
            }

            /// The flags that are set, one after the other, in the order they were declared, with
            /// their names. A flag is given when all its bits are set and no flag before it took
            /// them (so a combination declared before its parts stands for them), and flags with no
            /// bits are left out.
            pub fn iter_names(self) -> impl Iterator<Item = (&'static str, Self)> {
                let mut remaining = self.0;
                let mut next = 0;
                ::core::iter::from_fn(move || {
                    while next < Self::FLAGS.len() {
                        let (name, value) = Self::FLAGS[next];
                        next += 1;
                        if value != 0 && value & remaining == value {
                            remaining &= !value;
                            return Some((name, Self(value)));
                        }
                    }
                    None
                })
            }

            /// The flags that are set, one by one (see [`iter_names`](Self::iter_names)).
            pub fn iter(self) -> impl Iterator<Item = Self> {
                self.iter_names().map(|(_, flag)| flag)
            }
        }

        impl ::core::default::Default for $name {
            /// No flag set.
            fn default() -> Self {
                Self::empty()
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                if self.is_empty() {
                    // The name of a flag with no bits, if one was declared, else a mark.
                    let zero = Self::FLAGS.iter().find(|(_, value)| *value == 0);
                    return f.write_str(zero.map_or("(empty)", |(name, _)| name));
                }
                let mut separator = "";
                for (name, _) in self.iter_names() {
                    ::core::write!(f, "{separator}{name}")?;
                    separator = " | ";
                }
                Ok(())
            }
        }

        impl ::core::fmt::Binary for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::Binary::fmt(&self.0, f)
            }
        }

        impl ::core::fmt::Octal for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::Octal::fmt(&self.0, f)
            }
        }

        impl ::core::fmt::LowerHex for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::LowerHex::fmt(&self.0, f)
            }
        }

        impl ::core::fmt::UpperHex for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                ::core::fmt::UpperHex::fmt(&self.0, f)
            }
        }

        impl ::core::ops::BitOr for $name {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self {
                self.union(rhs)
            }
        }

        impl ::core::ops::BitOrAssign for $name {
            fn bitor_assign(&mut self, rhs: Self) {
                self.insert(rhs);
            }
        }

        impl ::core::ops::BitAnd for $name {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self {
                self.intersection(rhs)
            }
        }

        impl ::core::ops::BitAndAssign for $name {
            fn bitand_assign(&mut self, rhs: Self) {
                *self = self.intersection(rhs);
            }
        }

        impl ::core::ops::BitXor for $name {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self {
                self.symmetric_difference(rhs)
            }
        }

        impl ::core::ops::BitXorAssign for $name {
            fn bitxor_assign(&mut self, rhs: Self) {
                self.toggle(rhs);
            }
        }

        impl ::core::ops::Sub for $name {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self {
                self.difference(rhs)
            }
        }

        impl ::core::ops::SubAssign for $name {
            fn sub_assign(&mut self, rhs: Self) {
                self.remove(rhs);
            }
        }

        impl ::core::ops::Not for $name {
            type Output = Self;

            fn not(self) -> Self {
                self.complement()
            }
        }

        impl ::core::iter::FromIterator<$name> for $name {
            fn from_iter<I: ::core::iter::IntoIterator<Item = $name>>(iter: I) -> Self {
                let mut flags = Self::empty();
                flags.extend(iter);
                flags
            }
        }

        impl ::core::iter::Extend<$name> for $name {
            fn extend<I: ::core::iter::IntoIterator<Item = $name>>(&mut self, iter: I) {
                for flag in iter {
                    self.insert(flag);
                }
            }
        }
    };
}

#[cfg(test)]
mod tests {
    bit_flags! {
        /// A set of flags to test with.
        struct Letters: u8 {
            const NONE = 0;
            const AB = Self::A.bits() | Self::B.bits();
            const A = 1 << 0;
            const B = 1 << 1;
            const C = 1 << 2;
        }
    }

    bit_flags! {
        struct Plain: u16 {
            const FIRST = 1;
            const LAST = 1 << 15;
        }
    }

    #[test]
    fn flags_combine_and_are_contained() {
        let both = Letters::A | Letters::C;

        assert!(both.contains(Letters::A));
        assert!(both.contains(Letters::C));
        assert!(both.contains(Letters::A | Letters::C));
        assert!(!both.contains(Letters::B));
        assert!(!Letters::A.contains(both));
    }

    #[test]
    fn no_flag_is_in_everything_and_in_nothing_alike() {
        assert!(Letters::C.contains(Letters::empty()));
        assert!(Letters::empty().contains(Letters::empty()));
        assert!(!Letters::empty().contains(Letters::A));
        assert!(!Letters::C.intersects(Letters::empty()));
        assert_eq!(Letters::NONE, Letters::empty());
        assert_eq!(Letters::default(), Letters::empty());
        assert!(Letters::empty().is_empty());
    }

    #[test]
    fn the_set_operations() {
        let a_b = Letters::A | Letters::B;
        let b_c = Letters::B | Letters::C;

        assert_eq!(a_b & b_c, Letters::B);
        assert_eq!(a_b ^ b_c, Letters::A | Letters::C);
        assert_eq!(a_b - b_c, Letters::A);
        assert_eq!(a_b.union(b_c), Letters::A | Letters::B | Letters::C);
        assert!(a_b.intersects(b_c));
        assert!(!Letters::A.intersects(Letters::C));
    }

    #[test]
    fn not_is_the_declared_flags_that_are_missing() {
        assert_eq!(!Letters::A, Letters::B | Letters::C);
        assert_eq!(!Letters::all(), Letters::empty());
        assert_eq!(!Letters::empty(), Letters::all());
        // Never a bit that no flag has.
        assert_eq!((!Letters::A).bits(), 0b110);
    }

    #[test]
    fn all_is_every_flag_and_bits_are_the_integer() {
        assert_eq!(Letters::all().bits(), 0b111);
        assert!(Letters::all().is_all());
        assert!(!Letters::A.is_all());
        assert_eq!(Plain::all().bits(), 1 | (1 << 15));
    }

    #[test]
    fn bits_that_are_not_flags_are_refused_or_cut_off() {
        assert_eq!(Letters::from_bits(0b101), Some(Letters::A | Letters::C));
        assert_eq!(Letters::from_bits(0b1000), None);
        assert_eq!(Letters::from_bits(0b1001), None);
        assert_eq!(Letters::from_bits_truncate(0b1101), Letters::A | Letters::C);
        assert_eq!(Letters::from_bits(0), Some(Letters::empty()));
    }

    #[test]
    fn flags_change_in_place() {
        let mut flags = Letters::A;

        flags |= Letters::B;
        assert_eq!(flags, Letters::AB);
        flags -= Letters::A;
        assert_eq!(flags, Letters::B);
        flags ^= Letters::B | Letters::C;
        assert_eq!(flags, Letters::C);
        flags &= Letters::A | Letters::C;
        assert_eq!(flags, Letters::C);
        flags.insert(Letters::A);
        flags.remove(Letters::C);
        assert_eq!(flags, Letters::A);
        flags.toggle(Letters::A | Letters::B);
        assert_eq!(flags, Letters::B);
        flags.set(Letters::C, true);
        flags.set(Letters::B, false);
        assert_eq!(flags, Letters::C);
    }

    #[test]
    fn flags_are_listed_in_the_order_they_were_declared_and_a_combination_stands_for_its_parts() {
        let names = |flags: Letters| -> Vec<&'static str> {
            flags.iter_names().map(|(name, _)| name).collect()
        };

        assert_eq!(names(Letters::C | Letters::A), ["A", "C"]);
        // `AB` is declared before `A` and `B`, so it stands for them when both are set.
        assert_eq!(names(Letters::A | Letters::B), ["AB"]);
        assert_eq!(names(Letters::A | Letters::B | Letters::C), ["AB", "C"]);
        assert_eq!(names(Letters::empty()), Vec::<&str>::new());
        let flags: Vec<_> = (Letters::A | Letters::B | Letters::C).iter().collect();
        assert_eq!(flags, [Letters::AB, Letters::C]);
    }

    #[test]
    fn flags_collect_from_flags() {
        let flags: Letters = [Letters::A, Letters::C].into_iter().collect();
        assert_eq!(flags, Letters::A | Letters::C);

        let mut more = Letters::B;
        more.extend([Letters::A]);
        assert_eq!(more, Letters::AB);
    }

    #[test]
    fn flags_are_debug_printed_by_name() {
        assert_eq!(format!("{:?}", Letters::A), "A");
        assert_eq!(format!("{:?}", Letters::A | Letters::C), "A | C");
        assert_eq!(format!("{:?}", Letters::all()), "AB | C");
        // A flag with no bits names the empty set.
        assert_eq!(format!("{:?}", Letters::empty()), "NONE");
        // Without one, a mark does.
        assert_eq!(format!("{:?}", Plain::default()), "(empty)");
        assert_eq!(format!("{:?}", Plain::all()), "FIRST | LAST");
    }

    #[test]
    fn flags_print_their_bits_in_other_bases() {
        let flags = Letters::A | Letters::C;

        assert_eq!(format!("{flags:b}"), "101");
        assert_eq!(format!("{flags:o}"), "5");
        assert_eq!(format!("{flags:x}"), "5");
        assert_eq!(format!("{:X}", Plain::LAST), "8000");
        assert_eq!(format!("{:#06b}", Letters::A), "0b0001");
    }

    #[test]
    fn flags_can_be_compared_and_hashed() {
        use std::collections::HashSet;

        let mut set = HashSet::new();
        set.insert(Letters::A | Letters::B);
        assert!(set.contains(&Letters::AB));
        assert!(!set.contains(&Letters::A));
    }

    #[test]
    fn flags_can_be_used_in_constants() {
        const BOTH: Letters = Letters::A.union(Letters::C);
        const FIRST: Letters = Letters::from_bits_truncate(0b1111);

        assert!(BOTH.contains(Letters::C));
        assert!(FIRST.is_all());
    }
}
