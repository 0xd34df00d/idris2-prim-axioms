module Data.Bits.Verified.Prim

import Data.Bits as B

import Data.Bits.NonEmpty
import Data.Bits.Repr
import public Data.Bits.Verified as R
import Data.Bits.Verified.Repr
import Data.Fin.Order
import Data.Fin.Sub
import Data.Nat.Utils

%default total

export
interface (VerifiedBits repr, NonEmptyBits prim) => IsModelOf repr prim | prim where
  prim2repr : (0 _ : prim) -> repr
  prim2repr _ = believe_me "prim2repr"

  repr2prim : (0 _ : repr) -> prim
  repr2prim _ = believe_me "repr2prim"

export IsModelOf (UnsignedBV 8)  Bits8  where
export IsModelOf (UnsignedBV 16) Bits16 where
export IsModelOf (UnsignedBV 32) Bits32 where
export IsModelOf (UnsignedBV 64) Bits64 where


bitSizesMatch : (0 prim : Type) ->
                IsModelOf repr prim =>
                bitSizeTy repr = bitSizeTy prim
bitSizesMatch _ = believe_me "bitSizesMatch"

homoZeros : IsModelOf repr prim =>
            prim2repr {prim} B.zeroBits = B.zeroBits
homoZeros = believe_me "homoZeros"

homoOnes : IsModelOf repr prim =>
           prim2repr {prim} B.oneBits = B.oneBits
homoOnes = believe_me "homoOnes"

homoAnd : IsModelOf repr prim =>
          (0 v1, v2 : prim) ->
          prim2repr (v1 .&. v2) = prim2repr v1 .&. prim2repr v2
homoAnd _ _ = believe_me "homoAnd"

homoOr : IsModelOf repr prim =>
         (0 v1, v2 : prim) ->
         prim2repr (v1 .|. v2) = prim2repr v1 .|. prim2repr v2
homoOr _ _ = believe_me "homoOr"

homoComplement : IsModelOf repr prim =>
                 (0 v : prim) ->
                 prim2repr (complement v) = complement (prim2repr v)
homoComplement _ = believe_me "homoComplement"

homoShiftL : IsModelOf repr prim =>
             (0 v : prim) ->
             (0 sPrim : Fin (bitSizeTy prim)) ->
             (0 sRepr : Fin (bitSizeTy repr)) ->
             (0 _ : finToNat sPrim = finToNat sRepr) ->
             prim2repr (v `shiftL` bitsToIndexTy prim sPrim) = prim2repr v `shiftL` bitsToIndexTy repr sRepr
homoShiftL _ _ _ _ = believe_me "homoShiftL"

homoShiftR : IsModelOf repr prim =>
             (0 v : prim) ->
             (0 sPrim : Fin (bitSizeTy prim)) ->
             (0 sRepr : Fin (bitSizeTy repr)) ->
             (0 _ : finToNat sPrim = finToNat sRepr) ->
             prim2repr (v `shiftR` bitsToIndexTy prim sPrim) = prim2repr v `shiftR` bitsToIndexTy repr sRepr
homoShiftR _ _ _ _ = believe_me "homoShiftR"

prim2reprInjective : IsModelOf repr prim =>
                     {0 v1, v2 : prim} ->
                     prim2repr v1 = prim2repr v2 ->
                     v1 = v2
prim2reprInjective _ = believe_me "prim2reprInjective"

toNumEqual : IsModelOf repr prim =>
             (0 v : prim) ->
             toNum v = toNum (prim2repr v)
toNumEqual _ = believe_me "toNumEqual"

zeroIndexesEqual : (0 ty1, ty2 : Type) ->
                   NonEmptyBits ty1 =>
                   NonEmptyBits ty2 =>
                   finToNat (zeroIndexTy ty1) = finToNat (zeroIndexTy ty2)
zeroIndexesEqual ty1 ty2 = sym (zeroIndexIsZeroTy ty1) `trans` zeroIndexIsZeroTy ty2

public export
[viaModel] (IsModelOf repr prim) => VerifiedBits prim where
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
  andRightLess v1 v2 = rewrite toNumEqual (v1 .&. v2) in
                       rewrite toNumEqual v2 in
                       rewrite homoAnd v1 v2 in
                               andRightLess _ _

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
  orRightLess v1 v2 = rewrite toNumEqual (v1 .|. v2) in
                      rewrite toNumEqual v2 in
                      rewrite homoOr v1 v2 in
                              orRightLess _ _

  complementInvolutive v = prim2reprInjective $ rewrite homoComplement (complement v) in
                                                rewrite homoComplement v in
                                                        complementInvolutive (prim2repr v)

  shiftLZero v = prim2reprInjective $ homoShiftL v _ _ (zeroIndexesEqual prim repr)
                              `trans` shiftLZero (prim2repr v)
  shiftRZero v = prim2reprInjective $ homoShiftR v _ _ (zeroIndexesEqual prim repr)
                              `trans` shiftRZero (prim2repr v)

  shiftRBounded v s = rewrite toNumEqual (v `shiftR` bitsToIndexTy prim s) in
                      rewrite homoShiftR v s (rewrite bitSizesMatch prim in s) Refl in
                              shiftRBounded (prim2repr v) (rewrite bitSizesMatch prim in s)

public export %inline
vb8  : VerifiedBits Bits8
vb8 = viaModel

public export %inline
vb16 : VerifiedBits Bits16
vb16 = viaModel

public export %inline
vb32 : VerifiedBits Bits32
vb32 = viaModel

public export %inline
vb64 : VerifiedBits Bits64
vb64 = viaModel
