use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem, Shl, Shr, Sub};

use num_traits::{
  AsPrimitive, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub,
  FromPrimitive, Num, NumCast, One, PrimInt, Saturating, ToPrimitive, Zero,
};

/// A zero-sized type representing an unsigned integer which is zero bits wide.
///
/// This type implements the `num_traits::PrimInt` trait and all of its
/// dependencies. The `Div<UZero>::div()`, `Rem<UZero>::rem()`, and
/// `One::one()` functions all panic as they require support for values higher
/// than zero.
#[derive(Copy, Clone, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct UZero();

macro_rules! stub0 {
  ($name: ident) => {
    #[inline(always)]
    fn $name() -> UZero {
      UZero()
    }
  };
}

macro_rules! stub1 {
  ($name: ident) => {
    stub1!($name, UZero, UZero());
  };
  ($name: ident, $t: ty, $e: expr) => {
    #[inline(always)]
    fn $name(self) -> $t {
      $e
    }
  };
}

macro_rules! stub2 {
  ($name: ident) => {
    stub2!($name, UZero);
  };
  ($name: ident, $t: ty) => {
    stub2!($name, $t, UZero());
  };
  ($name: ident, $t: ty, $re: expr) => {
    #[inline(always)]
    fn $name(self, _: $t) -> UZero {
      $re
    }
  };
}

macro_rules! stub2_checked {
  ($name: ident, $re: expr) => {
    #[inline(always)]
    fn $name(&self, _: &UZero) -> Option<UZero> {
      $re
    }
  };
}

macro_rules! stub_as {
  ($t: ty, $e: expr) => {
    impl AsPrimitive<$t> for UZero {
      #[inline(always)]
      fn as_(self) -> $t {
        $e
      }
    }
  };
}

impl Debug for UZero {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Debug::fmt(&0, f)
  }
}

impl Display for UZero {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Display::fmt(&0, f)
  }
}

impl Bounded for UZero {
  stub0!(min_value);
  stub0!(max_value);
}

impl Add for UZero {
  type Output = UZero;
  stub2!(add);
}

impl Sub for UZero {
  type Output = UZero;
  stub2!(sub);
}

impl Div for UZero {
  type Output = UZero;
  stub2!(div, UZero, panic!("division by zero"));
}

impl Rem for UZero {
  type Output = UZero;
  stub2!(rem, UZero, panic!("division by zero"));
}

impl Mul for UZero {
  type Output = UZero;
  stub2!(mul);
}

impl CheckedAdd for UZero {
  stub2_checked!(checked_add, Some(UZero()));
}

impl CheckedSub for UZero {
  stub2_checked!(checked_sub, Some(UZero()));
}

impl CheckedDiv for UZero {
  stub2_checked!(checked_div, None);
}

impl CheckedMul for UZero {
  stub2_checked!(checked_mul, Some(UZero()));
}

impl Saturating for UZero {
  stub2!(saturating_add);
  stub2!(saturating_sub);
}

impl Shr<usize> for UZero {
  type Output = UZero;
  stub2!(shr, usize);
}

impl Shl<usize> for UZero {
  type Output = UZero;
  stub2!(shl, usize);
}

impl BitAnd for UZero {
  type Output = UZero;
  stub2!(bitand);
}

impl BitOr for UZero {
  type Output = UZero;
  stub2!(bitor);
}

impl BitXor for UZero {
  type Output = UZero;
  stub2!(bitxor);
}

impl Not for UZero {
  type Output = UZero;
  stub1!(not);
}

impl Zero for UZero {
  stub0!(zero);

  fn is_zero(&self) -> bool {
    true
  }
}

impl One for UZero {
  fn one() -> Self {
    panic!("UZero cannot represent one")
  }
}

impl Num for UZero {
  type FromStrRadixErr = ();

  fn from_str_radix(
    str: &str,
    _radix: u32,
  ) -> Result<Self, Self::FromStrRadixErr> {
    if str == "0" || str == "+0" {
      Ok(UZero())
    } else {
      Err(())
    }
  }
}

impl NumCast for UZero {
  fn from<T: ToPrimitive>(n: T) -> Option<Self> {
    match n.to_u8() {
      Some(0) => Some(UZero()),
      _ => None,
    }
  }
}

impl FromPrimitive for UZero {
  fn from_i64(n: i64) -> Option<Self> {
    if n == 0 {
      Some(UZero())
    } else {
      None
    }
  }

  fn from_u64(n: u64) -> Option<Self> {
    if n == 0 {
      Some(UZero())
    } else {
      None
    }
  }
}

impl ToPrimitive for UZero {
  fn to_i64(&self) -> Option<i64> {
    Some(0)
  }

  fn to_u64(&self) -> Option<u64> {
    Some(0)
  }
}

impl PrimInt for UZero {
  stub1!(count_ones, u32, 0);
  stub1!(count_zeros, u32, 0);
  stub1!(leading_zeros, u32, 0);
  stub1!(trailing_zeros, u32, 0);
  stub2!(rotate_left, u32);
  stub2!(rotate_right, u32);
  stub2!(signed_shl, u32);
  stub2!(signed_shr, u32);
  stub2!(unsigned_shl, u32);
  stub2!(unsigned_shr, u32);
  stub1!(swap_bytes);

  fn from_be(_: Self) -> Self {
    UZero()
  }

  fn from_le(_: Self) -> Self {
    UZero()
  }

  stub1!(to_be);
  stub1!(to_le);
  stub2!(pow, u32);
}

stub_as!(u8, 0);
stub_as!(i8, 0);
stub_as!(u16, 0);
stub_as!(i16, 0);
stub_as!(u32, 0);
stub_as!(i32, 0);
stub_as!(u64, 0);
stub_as!(i64, 0);
stub_as!(u128, 0);
stub_as!(i128, 0);
stub_as!(usize, 0);
stub_as!(isize, 0);
stub_as!(f32, 0.0);
stub_as!(f64, 0.0);
stub_as!(bool, false);

#[cfg(test)]
mod tests {
  use crate::UZero;
  use num_traits::Zero;
  use std::mem::size_of;

  #[test]
  fn is_zst() {
    assert_eq!(size_of::<UZero>(), 0);
  }

  #[test]
  fn it_works() {
    let z = UZero::zero();
    assert_eq!(z + z * z, z);
    assert_eq!(z.to_string(), "0");
  }
}
