module Data.Bits.NonEmpty

import Data.Bits as B

import Data.Nat.Utils

%default total

public export
bitSizeTy : (0 ty : Type) ->
            FiniteBits ty =>
            Nat
bitSizeTy ty = bitSize {a = ty}

public export %inline
bitsToIndexTy : (0 ty : Type) ->
                FiniteBits ty =>
                Fin (bitSizeTy ty) ->
                Index {a = ty}
bitsToIndexTy ty = bitsToIndex {a = ty}

public export
interface FiniteBits ty => NonEmptyBits ty where
  bitSizeNonZero : bitSizeTy ty = S (pred (bitSizeTy ty))

  toNum : ty -> Nat

  zeroIndex : Fin (bitSizeTy ty)
  zeroIndexIsZero : Z = finToNat zeroIndex

public export
bitSizeNonZeroTy : (0 ty : Type) ->
                   NonEmptyBits ty =>
                   bitSizeTy ty = S (pred (bitSizeTy ty))
bitSizeNonZeroTy ty = bitSizeNonZero {ty}

public export
zeroIndexTy : (0 ty : Type) ->
              NonEmptyBits ty =>
              Fin (bitSizeTy ty)
zeroIndexTy ty = zeroIndex {ty}

export
zeroIndexIsZeroTy : (0 ty : Type) ->
                    NonEmptyBits ty =>
                    Z = finToNat (zeroIndexTy ty)
zeroIndexIsZeroTy ty = zeroIndexIsZero {ty}

export
zeroIndexesEqual : (0 ty1, ty2 : Type) ->
                   NonEmptyBits ty1 =>
                   NonEmptyBits ty2 =>
                   finToNat (zeroIndexTy ty1) = finToNat (zeroIndexTy ty2)
zeroIndexesEqual ty1 ty2 = sym (zeroIndexIsZeroTy ty1) `trans` zeroIndexIsZeroTy ty2

export %inline
NonEmptyBits Bits8  where
  bitSizeNonZero = Refl
  toNum = cast
  zeroIndex = FZ
  zeroIndexIsZero = Refl

export %inline
NonEmptyBits Bits16 where
  bitSizeNonZero = Refl
  toNum = cast
  zeroIndex = FZ
  zeroIndexIsZero = Refl

export %inline
NonEmptyBits Bits32 where
  bitSizeNonZero = Refl
  toNum = cast
  zeroIndex = FZ
  zeroIndexIsZero = Refl

export %inline
NonEmptyBits Bits64 where
  bitSizeNonZero = Refl
  toNum = cast
  zeroIndex = FZ
  zeroIndexIsZero = Refl
