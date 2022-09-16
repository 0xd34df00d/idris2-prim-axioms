module Data.Bits.Verified.Prim

import Data.Bits as B

import Data.Bits.Axioms
import Data.Bits.Axioms.MetaMath
import Data.Bits.Repr
import Data.Bits.Verified as R
import Data.Bits.Verified.Repr
import Data.Fin.Order

%default total

interface FiniteBits prim => NonEmptyBits prim where
  bitSizeNonZero : S (pred (bitSize {a = prim})) = bitSize {a = prim}

NonEmptyBits Bits8  where bitSizeNonZero = Refl
NonEmptyBits Bits16 where bitSizeNonZero = Refl
NonEmptyBits Bits32 where bitSizeNonZero = Refl
NonEmptyBits Bits64 where bitSizeNonZero = Refl


export
(IsModelOf _ prim, NonEmptyBits prim, Cast prim Nat) => VerifiedBits prim where
  toNum v = let %hint
                smaller : cast v `LT` bound (bitSize {a = prim})
                smaller = believe_me ()
             in natToFinLT (cast v)

  andRightId v = prim2reprInjective $ homoAnd v B.oneBits
                              `trans` cong (prim2repr v .&.) homoOnes
                              `trans` R.andRightId (prim2repr v)
  andLeftId v  = prim2reprInjective $ homoAnd _ v
                              `trans` cong (.&. prim2repr v) homoOnes
                              `trans` R.andLeftId (prim2repr v)
  andRightZero v = prim2reprInjective $ homoAnd v _
                                `trans` cong (prim2repr v .&.) homoZeros
                                `trans` R.andRightZero (prim2repr v)
                                `trans` sym homoZeros
  andLeftZero v  = prim2reprInjective $ homoAnd _ v
                                `trans` cong (.&. prim2repr v) homoZeros
                                `trans` R.andLeftZero (prim2repr v)
                                `trans` sym homoZeros
  andCommutes v1 v2 = prim2reprInjective $ homoAnd v1 v2
                                   `trans` R.andCommutes _ _
                                   `trans` sym (homoAnd v2 v1)

  bitsToIndex' f = bitsToIndex {a = prim} $ rewrite sym $ bitSizeNonZero {prim = prim} in f
