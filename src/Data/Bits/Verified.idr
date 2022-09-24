module Data.Bits.Verified

import Data.Bits as B

import public Data.Bits.NonEmpty
import Data.Fin.Order
import Data.Fin.Sub
import Data.Nat.Utils

%default total

public export
interface NonEmptyBits ty => VerifiedBits ty where
  -- Properties of `and`
  andCommutes  : (v1, v2 : ty) ->
                 v1 .&. v2 = v2 .&. v1

  andRightId   : (v : ty) ->
                 v .&. B.oneBits = v
  andLeftId    : (v : ty) ->
                 B.oneBits .&. v = v
  andLeftId v  = andCommutes oneBits v `trans` andRightId v

  andRightZero : (v : ty) ->
                 v .&. B.zeroBits = B.zeroBits
  andLeftZero  : (v : ty) ->
                 B.zeroBits .&. v = B.zeroBits
  andLeftZero v = andCommutes zeroBits v `trans` andRightZero v

  andRightLess : (v1, v2 : ty) ->
                 toNum (v1 .&. v2) `FLTE` toNum v2
  andLeftLess  : (v1, v2 : ty) ->
                 toNum (v1 .&. v2) `FLTE` toNum v1
  andLeftLess v1 v2 = replace {p = \v => toNum v `FLTE` toNum v1} (sym $ andCommutes v1 v2) (andRightLess v2 v1)


  -- Properties of `or`
  orCommutes : (v1, v2 : ty) ->
               v1 .|. v2 = v2 .|. v1

  orRightId  : (v : ty) ->
               v .|. B.zeroBits = v
  orLeftId   : (v : ty) ->
               B.zeroBits .|. v = v
  orLeftId v = orCommutes zeroBits v `trans` orRightId v

  orRightOne : (v : ty) ->
               v .|. B.oneBits = B.oneBits
  orLeftOne  : (v : ty) ->
               B.oneBits .|. v= B.oneBits
  orLeftOne v = orCommutes oneBits v `trans` orRightOne v

  orRightLess : (v1, v2 : ty) ->
                toNum v2 `FLTE` toNum (v1 .|. v2)
  orLeftLess  : (v1, v2 : ty) ->
                toNum v1 `FLTE` toNum (v1 .|. v2)
  orLeftLess v1 v2 = replace {p = \v => toNum v1 `FLTE` toNum v} (sym $ orCommutes v1 v2) (orRightLess v2 v1)

  -- Properties of `complement`
  complementInvolutive : (v : ty) ->
                         complement (complement v) = v

  -- Properties of shifts
  shiftLZero : (v : ty) ->
               v `shiftL` bitsToIndexTy ty (zeroIndexTy ty) = v
  shiftRZero : (v : ty) ->
               v `shiftR` bitsToIndexTy ty (zeroIndexTy ty) = v
  shiftRBounded : (v : ty) ->
                  (s : Fin (bitSizeTy ty)) ->
                  toNum (v `shiftR` bitsToIndexTy ty s) `FLTE` last' (bound $ bitSizeTy ty `natSubFin` s)

infixl 8 .>>.**

export
(.>>.**) : {ty : Type} ->
           VerifiedBits ty =>
           (v : ty) ->
           (s : Fin (bitSizeTy ty)) ->
           (res : ty ** toNum res `FLTE` last' (bound $ bitSizeTy ty `natSubFin` s))
(.>>.**) {ty} v s = (v `shiftR` bitsToIndexTy ty s ** shiftRBounded v s)
