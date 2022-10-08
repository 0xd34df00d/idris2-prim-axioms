module Data.Bits.Verified.Interface

import Data.Bits as B

import public Data.Bits.NonEmpty
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

