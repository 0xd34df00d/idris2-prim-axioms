module Data.Bits.NonEmpty

import Data.Bits as B

%default total

public export
interface FiniteBits ty => NonEmptyBits ty where
  bitSizeNonZero : bitSize {a = ty} = S (pred (bitSize {a = ty}))

export NonEmptyBits Bits8  where bitSizeNonZero = Refl
export NonEmptyBits Bits16 where bitSizeNonZero = Refl
export NonEmptyBits Bits32 where bitSizeNonZero = Refl
export NonEmptyBits Bits64 where bitSizeNonZero = Refl
