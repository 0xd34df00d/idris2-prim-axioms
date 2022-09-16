module Data.Bits.Verified.Prim

import Data.Bits as B

import Data.Bits.Axioms
import Data.Bits.Axioms.MetaMath
import Data.Bits.Repr
import Data.Bits.Verified as R
import Data.Bits.Verified.Repr
import Data.Fin.Order

%default total

interface FiniteBits ty => NonEmptyBits ty where
  bitSizeNonZero : S (pred (bitSize {a = ty})) = bitSize {a = ty}

NonEmptyBits Bits8  where bitSizeNonZero = Refl
NonEmptyBits Bits16 where bitSizeNonZero = Refl
NonEmptyBits Bits32 where bitSizeNonZero = Refl
NonEmptyBits Bits64 where bitSizeNonZero = Refl


export
interface (VerifiedBits repr, NonEmptyBits prim) => IsModelOf repr prim | prim where
  prim2repr : (0 _ : prim) -> repr
  prim2repr = believe_me ()

  repr2prim : (0 _ : repr) -> prim
  repr2prim = believe_me ()

  homoZeros : prim2repr B.zeroBits = B.zeroBits
  homoZeros = believe_me ()

  homoOnes : prim2repr B.oneBits = B.oneBits
  homoOnes = believe_me ()

  homoAnd : (0 v1, v2 : prim)
         -> prim2repr (v1 .&. v2) = prim2repr v1 .&. prim2repr v2
  homoAnd = believe_me ()

  homoShiftL : (0 v : prim)
            -> (0 sPrim : Fin (bitSize {a = prim}))
            -> (0 sRepr : Fin (bitSize {a = repr}))
            -> (0 _ : finToNat sPrim = finToNat sRepr)
            -> prim2repr (v `shiftL` bitsToIndex {a = prim} sPrim) = prim2repr v `shiftL` bitsToIndex {a = repr} sRepr
  homoShiftL = believe_me ()

  prim2reprInjective : {0 v1, v2 : prim}
                    -> prim2repr v1 = prim2repr v2
                    -> v1 = v2
  prim2reprInjective = believe_me ()

export IsModelOf (UnsignedBV 8)  Bits8  where
export IsModelOf (UnsignedBV 16) Bits16 where
export IsModelOf (UnsignedBV 32) Bits32 where
export IsModelOf (UnsignedBV 64) Bits64 where


export
(IsModelOf _ prim, Cast prim Nat) => VerifiedBits prim where
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

  zeroIndex = rewrite sym $ bitSizeNonZero {ty = prim} in FZ
  zeroIndexIsZero = Refl

  shiftLZero v = let primZero : Fin (bitSize {a = prim})
                     primZero = rewrite sym $ bitSizeNonZero {ty = prim} in FZ
                  in prim2reprInjective $ homoShiftL v primZero zeroIndex (sym zeroIndexIsZero)
                                  `trans` R.shiftLZero (prim2repr v)
