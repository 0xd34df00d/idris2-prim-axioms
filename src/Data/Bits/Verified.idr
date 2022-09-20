module Data.Bits.Verified

import Data.Bits as B

import Data.Bits.Axioms.MetaMath
import public Data.Bits.NonEmpty
import Data.Fin.Order

%default total

public export
interface NonEmptyBits ty => VerifiedBits ty where
  andCommutes  : (v1, v2 : ty)
              -> v1 .&. v2 = v2 .&. v1
  andRightId   : (v : ty)
              -> v .&. B.oneBits = v
  andLeftId    : (v : ty)
              -> B.oneBits .&. v = v
  andLeftId v  = andCommutes oneBits v `trans` andRightId v
  andRightZero : (v : ty)
              -> v .&. B.zeroBits = B.zeroBits
  andLeftZero  : (v : ty)
              -> B.zeroBits .&. v = B.zeroBits
  andLeftZero v = andCommutes zeroBits v `trans` andRightZero v
  andRightLess : (v1, v2 : ty)
              -> toNum (v1 .&. v2) `FLTE` toNum v2
  andLeftLess  : (v1, v2 : ty)
              -> toNum (v1 .&. v2) `FLTE` toNum v1
  andLeftLess v1 v2 = rewrite andCommutes v1 v2 in andRightLess v2 v1

  orCommutes : (v1, v2 : ty)
            -> v1 .|. v2 = v2 .|. v1
  orRightId  : (v : ty)
            -> v .|. B.zeroBits = v
  orLeftId   : (v : ty)
            -> B.zeroBits .|. v = v
  orLeftId v = orCommutes zeroBits v `trans` orRightId v
  orRightOne : (v : ty)
            -> v .|. B.oneBits = B.oneBits
  orLeftOne  : (v : ty)
            -> B.oneBits .|. v= B.oneBits
  orLeftOne v = orCommutes oneBits v `trans` orRightOne v

  zeroIndex : Fin (bitSize {a = ty})
  zeroIndexIsZero : Z = finToNat zeroIndex

  shiftLZero : (v : ty)
            -> v `shiftL` bitsToIndex {a = ty} zeroIndex = v
  shiftRZero : (v : ty)
            -> v `shiftR` bitsToIndex {a = ty} zeroIndex = v
  shiftRBounded : (v : ty)
               -> (s : Fin (bitSize {a = ty}))
               -> toNum (v `shiftR` bitsToIndex {a = ty} s) `FLTE` last' (bound $ bitSize {a = ty} `natSubFin` s)
