module Data.Bits.NonEmpty

import Data.Bits as B

import Data.Bits.Axioms.MetaMath

%default total

public export
bitSizeTy : (0 ty : Type) -> FiniteBits ty => Nat
bitSizeTy ty = bitSize {a = ty}

public export
interface FiniteBits ty => NonEmptyBits ty where
  bitSizeNonZero : bitSizeTy ty = S (pred (bitSizeTy ty))

  toNum : ty -> Fin (bound $ bitSizeTy ty)

toNumBits : (FiniteBits ty, Cast ty Nat) => ty -> Fin (bound $ bitSizeTy ty)
toNumBits v = let %hint
                  smaller : cast v `LT` bound (bitSizeTy ty)
                  smaller = believe_me ()
               in natToFinLT (cast v)

export
NonEmptyBits Bits8  where
  bitSizeNonZero = Refl
  toNum = toNumBits

export
NonEmptyBits Bits16 where
  bitSizeNonZero = Refl
  toNum = toNumBits

export
NonEmptyBits Bits32 where
  bitSizeNonZero = Refl
  toNum = toNumBits

export
NonEmptyBits Bits64 where
  bitSizeNonZero = Refl
  toNum = toNumBits
