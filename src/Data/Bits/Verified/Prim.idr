module Data.Bits.Verified.Prim

import Data.Bits as B

import Data.Bits.Axioms.MetaMath
import Data.Bits.NonEmpty
import Data.Bits.Repr
import Data.Bits.Verified as R
import Data.Bits.Verified.Repr
import Data.Fin.Order

%default total

export
interface (VerifiedBits repr, NonEmptyBits prim) => IsModelOf repr prim | prim where
  prim2repr : (0 _ : prim) -> repr
  prim2repr = believe_me ()

  repr2prim : (0 _ : repr) -> prim
  repr2prim = believe_me ()

export IsModelOf (UnsignedBV 8)  Bits8  where
export IsModelOf (UnsignedBV 16) Bits16 where
export IsModelOf (UnsignedBV 32) Bits32 where
export IsModelOf (UnsignedBV 64) Bits64 where


bitSizesMatch : (0 prim : Type)
             -> IsModelOf repr prim
             => bitSizeTy repr = bitSizeTy prim
bitSizesMatch = believe_me ()

homoZeros : IsModelOf repr prim
         => prim2repr {prim = prim} B.zeroBits = B.zeroBits
homoZeros = believe_me ()

homoOnes : IsModelOf repr prim
        => prim2repr {prim = prim} B.oneBits = B.oneBits
homoOnes = believe_me ()

homoAnd : IsModelOf repr prim
       => (0 v1, v2 : prim)
       -> prim2repr (v1 .&. v2) = prim2repr v1 .&. prim2repr v2
homoAnd = believe_me ()

homoOr : IsModelOf repr prim
      => (0 v1, v2 : prim)
      -> prim2repr (v1 .|. v2) = prim2repr v1 .|. prim2repr v2
homoOr = believe_me ()

homoShiftL : IsModelOf repr prim
          => (0 v : prim)
          -> (0 sPrim : Fin (bitSizeTy prim))
          -> (0 sRepr : Fin (bitSizeTy repr))
          -> (0 _ : finToNat sPrim = finToNat sRepr)
          -> prim2repr (v `shiftL` bitsToIndexTy prim sPrim) = prim2repr v `shiftL` bitsToIndexTy repr sRepr
homoShiftL = believe_me ()

homoShiftR : IsModelOf repr prim
          => (0 v : prim)
          -> (0 sPrim : Fin (bitSizeTy prim))
          -> (0 sRepr : Fin (bitSizeTy repr))
          -> (0 _ : finToNat sPrim = finToNat sRepr)
          -> prim2repr (v `shiftR` bitsToIndexTy prim sPrim) = prim2repr v `shiftR` bitsToIndexTy repr sRepr
homoShiftR = believe_me ()

prim2reprInjective : IsModelOf repr prim
                  => {0 v1, v2 : prim}
                  -> prim2repr v1 = prim2repr v2
                  -> v1 = v2
prim2reprInjective = believe_me ()

toNumEqual : IsModelOf repr prim
          => (0 v : prim)
          -> toNum v ~=~ toNum (prim2repr v)
toNumEqual v = believe_me ()


export
(IsModelOf repr prim) => VerifiedBits prim where
  andCommutes v1 v2 = prim2reprInjective $ homoAnd v1 v2
                                   `trans` andCommutes _ _
                                   `trans` sym (homoAnd v2 v1)
  andRightId v = prim2reprInjective $ homoAnd v oneBits
                              `trans` cong (prim2repr v .&.) homoOnes
                              `trans` andRightId (prim2repr v)
  andRightZero v = prim2reprInjective $ homoAnd v _
                                `trans` cong (prim2repr v .&.) homoZeros
                                `trans` andRightZero (prim2repr v)
                                `trans` sym homoZeros

  orCommutes v1 v2 = prim2reprInjective $ homoOr v1 v2
                                  `trans` orCommutes _ _
                                  `trans` sym (homoOr v2 v1)
  orRightId v = prim2reprInjective $ homoOr v zeroBits
                             `trans` cong (prim2repr v .|.) homoZeros
                             `trans` orRightId (prim2repr v)
  orRightOne v = prim2reprInjective $ homoOr v _
                              `trans` cong (prim2repr v .|.) homoOnes
                              `trans` orRightOne (prim2repr v)
                              `trans` sym homoOnes

  zeroIndex = rewrite bitSizeNonZeroTy prim in FZ
  zeroIndexIsZero = Refl

  shiftLZero v = prim2reprInjective $ homoShiftL v (rewrite bitSizeNonZeroTy prim in FZ) zeroIndex zeroIndexIsZero
                              `trans` shiftLZero (prim2repr v)
  shiftRZero v = prim2reprInjective $ homoShiftR v (rewrite bitSizeNonZeroTy prim in FZ) zeroIndex zeroIndexIsZero
                              `trans` shiftRZero (prim2repr v)

  shiftRBounded v s with ( shiftRBounded (prim2repr v) (rewrite bitSizesMatch prim in s)
                         , homoShiftR v s (rewrite bitSizesMatch prim in s) Refl
                         , toNumEqual (v `shiftR` bitsToIndexTy prim s)
                         )
    _ | (reprPrf, homoShiftRPrf, toNumEq) with (bitSizesMatch prim)
                                             | (bitSizeTy repr)
      _ | Refl | _ = rewrite toNumEq in
                     rewrite homoShiftRPrf in
                             reprPrf
