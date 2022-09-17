module Data.Bits.Verified

import Data.Bits as B

import Data.Bits.Axioms.MetaMath
import Data.Fin.Order

%default total

public export
interface FiniteBits ty => VerifiedBits ty where
  toNum : ty -> Fin (bound $ bitSize {a = ty})

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

  orCommutes : (v1, v2 : ty)
            -> v1 .|. v2 = v2 .|. v1
  orRightId  : (v : ty)
            -> v .|. B.zeroBits = v
  orLeftId   : (v : ty)
            -> B.zeroBits .|. v = v
  orLeftId v = orCommutes zeroBits v `trans` orRightId v

  zeroIndex : Fin (bitSize {a = ty})
  zeroIndexIsZero : Z = finToNat zeroIndex

  shiftLZero : (v : ty)
            -> v `shiftL` bitsToIndex {a = ty} zeroIndex = v
  shiftRZero : (v : ty)
            -> v `shiftR` bitsToIndex {a = ty} zeroIndex = v
  shiftRBounded : (v : ty)
               -> (s : Fin (bitSize {a = ty}))
               -> toNum (v `shiftR` bitsToIndex {a = ty} s) `FLTE` last' (bound $ bitSize {a = ty} `natSubFin` s)
