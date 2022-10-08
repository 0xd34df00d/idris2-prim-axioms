module Data.Bits.Verified.Operations

import Data.Bits

import Data.Bits.NonEmpty
import Data.Bits.Verified.Interface
import Data.Bounded
import Data.Fin.Order
import Data.Fin.Sub
import Data.Nat.Utils

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

infixl 8 .>>.|

||| Shift `v` of type `ty` by `s` bits to the right,
||| and wrap it into a `Fin` suitable for bit-indexing into `ty`
||| (for subsequent shifts, or accessing individual bits, etc).
|||
||| Algorithms on a bit type `ty` sometimes take a value of `ty`,
||| shift it right by some bits `s` and then use the result as an index for another shift.
||| This helper function is handy for this particular task:
||| ```idris example
||| ex : Bits8 -> Bits8
||| ex bs = bs `shiftR` (bs .>>.| 6)
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
(.>>.|) : VerifiedBits ty =>
          (v : ty) ->
          (s : Fin (bitSizeTy ty)) ->
          {auto 0 maxBound : bound (bitSizeTy ty `natSubFin` s) `LTE` bitSizeTy ty} ->
          Fin (bitSizeTy ty)
(.>>.|) v s = let MkBounded v prf = v .>>.** s
               in natToFinLT (toNum v) {prf = prf `transitive` maxBound}

||| Proves `.>>|` behaves as a shift.
export
rightShiftBoundedPreserves : VerifiedBits ty =>
                             (v : ty) ->
                             (s : Fin (bitSizeTy ty)) ->
                             (maxBound : bound (bitSizeTy ty `natSubFin` s) `LTE` bitSizeTy ty) ->
                             finToNat (v .>>.| s) = toNum (v `shiftR` bitsToIndexTy ty s)
rightShiftBoundedPreserves v s maxBound = natToFinLtToNat _ {prf = shiftRBounded v s `transitive` maxBound}

public export %inline
asFin : NonEmptyBits ty =>
        Bounded ty n ->
        {auto 0 boundCorrect : n `LTE` bitSizeTy ty} ->
        Fin (bitSizeTy ty)
asFin (MkBounded v prf) = natToFinLT (toNum v) {prf = prf `transitive` boundCorrect}

infix 7 .&.**, **.&., .&.|, |.&.

||| An bit-`and` of two numbers `v1` and `v2`, with a proof that the result is less than `v2`.
|||
||| See also `.&.|`.
public export %inline
(.&.**) : VerifiedBits ty =>
          (v1, v2 : ty) ->
          Bounded ty (S (toNum v2))
v1 .&.** v2 = MkBounded (v1 .&. v2) (LTESucc $ andRightLess v1 v2)

||| An bit-`and` of two numbers `v1` and `v2`, with a proof that the result is less than `v1`.
|||
||| See also `|.&.`.
public export %inline
(**.&.) : VerifiedBits ty =>
          (v1, v2 : ty) ->
          Bounded ty (S (toNum v1))
v1 **.&. v2 = MkBounded (v1 .&. v2) (LTESucc $ andLeftLess v1 v2)

||| An bit-`and` of two numbers `v1` and `v2` of type `ty`, wrapped in a `Fin` suitable for bit-indexing into `ty`
||| (for subsequent shifts, or accessing individual bits, etc).
|||
||| This function requires the second operand to be less than the bit width of `ty`.
||| For the version that uses the first one, see `|.&.`.
|||
||| See also `.&.**`.
public export %inline
(.&.|) : VerifiedBits ty =>
         (v1, v2 : ty) ->
         {auto 0 maxBound : toNum v2 `LT` bitSizeTy ty} ->
         Fin (bitSizeTy ty)
v1 .&.| v2 = let MkBounded res prf = v1 .&.** v2
              in natToFinLT (toNum res) {prf = prf `transitive` maxBound}

||| An bit-`and` of two numbers `v1` and `v2` of type `ty`, wrapped in a `Fin` suitable for bit-indexing into `ty`
||| (for subsequent shifts, or accessing individual bits, etc).
|||
||| This function requires the first operand to be less than the bit width of `ty`.
||| For the version that uses the second one, see `.&.|`.
|||
||| See also `.&.**`.
public export %inline
(|.&.) : VerifiedBits ty =>
         (v1, v2 : ty) ->
         {auto 0 maxBound : toNum v1 `LT` bitSizeTy ty} ->
         Fin (bitSizeTy ty)
v1 |.&. v2 = let MkBounded res prf = v1 **.&. v2
              in natToFinLT (toNum res) {prf = prf `transitive` maxBound}
