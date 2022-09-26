module Data.Bits.Verified

import Data.Bits as B

import public Data.Bits.NonEmpty
import Data.Bounded
import Data.Fin.Order
import Data.Fin.Sub
import Data.Nat.Utils

%default total

public export
interface NonEmptyBits ty => VerifiedBits ty where
  -- Workaround bad codegen for all-0-interfaces
  dummy : Z = Z
  dummy = Refl

  -- Properties of `and`
  0 andCommutes  : (v1, v2 : ty) ->
                   v1 .&. v2 = v2 .&. v1

  0 andRightId   : (v : ty) ->
                   v .&. B.oneBits = v
  0 andLeftId    : (v : ty) ->
                   B.oneBits .&. v = v
  andLeftId v  = andCommutes oneBits v `trans` andRightId v

  0 andRightZero : (v : ty) ->
                   v .&. B.zeroBits = B.zeroBits
  0 andLeftZero  : (v : ty) ->
                   B.zeroBits .&. v = B.zeroBits
  andLeftZero v = andCommutes zeroBits v `trans` andRightZero v

  0 andRightLess : (v1, v2 : ty) ->
                   toNum (v1 .&. v2) `LTE` toNum v2
  0 andLeftLess  : (v1, v2 : ty) ->
                   toNum (v1 .&. v2) `LTE` toNum v1
  andLeftLess v1 v2 = replace {p = \v => toNum v `LTE` toNum v1} (sym $ andCommutes v1 v2) (andRightLess v2 v1)


  -- Properties of `or`
  0 orCommutes : (v1, v2 : ty) ->
                 v1 .|. v2 = v2 .|. v1

  0 orRightId  : (v : ty) ->
                 v .|. B.zeroBits = v
  0 orLeftId   : (v : ty) ->
                 B.zeroBits .|. v = v
  orLeftId v = orCommutes zeroBits v `trans` orRightId v

  0 orRightOne : (v : ty) ->
                 v .|. B.oneBits = B.oneBits
  0 orLeftOne  : (v : ty) ->
                 B.oneBits .|. v= B.oneBits
  orLeftOne v = orCommutes oneBits v `trans` orRightOne v

  0 orRightLess : (v1, v2 : ty) ->
                  toNum v2 `LTE` toNum (v1 .|. v2)
  0 orLeftLess  : (v1, v2 : ty) ->
                  toNum v1 `LTE` toNum (v1 .|. v2)
  orLeftLess v1 v2 = replace {p = \v => toNum v1 `LTE` toNum v} (sym $ orCommutes v1 v2) (orRightLess v2 v1)

  -- Properties of `complement`
  0 complementInvolutive : (v : ty) ->
                           complement (complement v) = v

  -- Properties of shifts
  0 shiftLZero : (v : ty) ->
                 v `shiftL` bitsToIndexTy ty (zeroIndexTy ty) = v
  0 shiftRZero : (v : ty) ->
                 v `shiftR` bitsToIndexTy ty (zeroIndexTy ty) = v
  0 shiftRBounded : (v : ty) ->
                    (s : Fin (bitSizeTy ty)) ->
                    toNum (v `shiftR` bitsToIndexTy ty s) `LT` bound (bitSizeTy ty `natSubFin` s)

infixl 8 .>>., .<<.
public export %inline
(.>>.), (.<<.) : Bits ty => ty -> Index {a = ty} -> ty
(.>>.) = shiftR
(.<<.) = shiftL

infixl 8 .>>.**

||| Shift `v` by `s` bits to the right, with a proof about the maximum value of the result.
|||
||| If type `ty` is `w` bits wide,
||| then shifting a value of `ty` right by `s` bits produces
||| a `res` that's less than `2 ^^ (w - s)`.
||| This function returns the result `res` along with the proof of this "less-than" relation.
|||
||| See also `.>>|`.
public export %inline
(.>>.**) : VerifiedBits ty =>
           (v : ty) ->
           (s : Fin (bitSizeTy ty)) ->
           Bounded ty (bound (bitSizeTy ty `natSubFin` s))
(.>>.**) v s = MkBounded (v `shiftR` bitsToIndexTy ty s) (shiftRBounded v s)

infixl 8 .>>|

||| Shift `v` by `s` bits to the right, wrapped in a type usable in subsequent shifts.
|||
||| Algorithms on a bit type `ty` sometimes take a value of `ty`,
||| shift it right by some bits `s` and then use the result as an index for another shift.
||| This helper function is handy for this particular task:
||| ```idris example
||| ex : Bits8 -> Bits8
||| ex bs = bs `shiftR` (bs .>>| 6)
||| ```
|||
||| Here, shifting a `Bits8` value to the right by `6` produces a value that's no bigger than `0b11 = 3`,
||| so it can be used a right-shift on a `Bits8` value.
|||
||| The `rightShiftBoundedPreserves` theorem proves that this indeed behaves as a right shift.
|||
||| @ v The value to shift right.
||| @ s The shift itself.
||| @ maxBound A proof that the value after the shift can be used as an index itself.
||| Most often, especially for statically known shifts, Idris is able to figure this out by itself.
public export %inline
(.>>|) : VerifiedBits ty =>
         (v : ty) ->
         (s : Fin (bitSizeTy ty)) ->
         {auto 0 maxBound : bound (bitSizeTy ty `natSubFin` s) `LTE` bitSizeTy ty} ->
         Fin (bitSizeTy ty)
(.>>|) v s = let MkBounded v prf = v .>>.** s
              in natToFinLT (toNum v) {prf = prf `transitive` maxBound}

||| Proves `.>>|` behaves as a shift.
export
rightShiftBoundedPreserves : VerifiedBits ty =>
                             (v : ty) ->
                             (s : Fin (bitSizeTy ty)) ->
                             (maxBound : bound (bitSizeTy ty `natSubFin` s) `LTE` bitSizeTy ty) ->
                             finToNat (v .>>| s) = toNum (v `shiftR` bitsToIndexTy ty s)
rightShiftBoundedPreserves v s maxBound = natToFinLtToNat _ {prf = shiftRBounded v s `transitive` maxBound}
