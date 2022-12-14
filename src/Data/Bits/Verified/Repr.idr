module Data.Bits.Verified.Repr

import Data.Bits as B
import Data.Fin
import Data.Fin.Extra
import Data.Vect
import Data.Vect.Properties.Index
import Data.Vect.Properties.Map
import Data.Vect.Properties.Tabulate

import Data.Bits.BitDef as B
import Data.Bits.Repr
import Data.Bits.Repr.Order
import Data.Bits.Verified.Interface
import Data.Fin.Order
import Data.Fin.Sub
import Data.Nat.Utils
import Data.Vect.Split
import Data.Vect.Utils

%default total

accBVLeftZero : {w : _} ->
                (bv : Vect w Bit) ->
                accBV (O :: bv) ~~~ accBV bv
accBVLeftZero {w = w} bv with (plusZeroRightNeutral $ bound w)
                            | (bound w + Z)
  _ | Refl | _ = plusZeroRightNeutral (accBV bv)

zeroPaddedBound : {n : _} ->
                  (m : _) ->
                  (right : Vect n Bit) ->
                  accBV (replicate m O ++ right) `FLT` last' (bound n)
zeroPaddedBound Z right = lastIsLast (accBV right)
zeroPaddedBound (S m) right = let pw = symmetric $ accBVLeftZero (replicate m O ++ right)
                               in fltePointwiseLeft (FS pw) (zeroPaddedBound m right)

shiftRBoundedImpl : {w : _} ->
                    (v : UnsignedBV w) ->
                    (s : Fin w) ->
                    getFinVal (bvToFin (v `shiftR` s)) `FLT` last' (bound $ w `natSubFin` s)
shiftRBoundedImpl (MkU bv) s with (splitRAtFin s bv)
  shiftRBoundedImpl (MkU _) s | TheSplit {n1 = n1, n2 = n2} before after eq
                                = rewrite natSubFinPlus n1 n2 s eq in
                                  rewrite plusCommutative n1 n2 in
                                          zeroPaddedBound n2 before

Ones : {w : _} -> Vect w Bit
Ones = replicate _ I

Zeros : {w : _} -> Vect w Bit
Zeros = replicate _ O

export
{w : _} -> VerifiedBits (UnsignedBV (S w)) where
  andCommutes (MkU bv1) (MkU bv2) = cong MkU $ vectorExtensionality (zipWith and bv1 bv2) (zipWith and bv2 bv1) f
    where
      f : (i : _) -> index i (zipWith B.and bv1 bv2) = index i (zipWith B.and bv2 bv1)
      f i = zipWithIndexLinear and bv1 bv2 i `trans`
            B.andCommutes _ _                `trans`
            sym (zipWithIndexLinear and bv2 bv1 i)

  andRightId (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv Ones) bv f
    where
      f : (i : _) -> index i (zipWith B.and bv Ones) = index i bv
      f i = zipWithIndexLinear and bv Ones i `trans`
            rewrite indexReplicate i I in B.andRightId _

  andRightZero (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv Zeros) Zeros f
    where
      f : (i : _) -> index i (zipWith B.and bv Zeros) = index i Zeros
      f i = zipWithIndexLinear and bv Zeros i `trans`
            rewrite indexReplicate i O in B.andRightZero _

  andRightLess (MkU bv1) (MkU bv2) = lteHomo _ _ (bvLteAndRight _ _)


  orCommutes (MkU bv1) (MkU bv2) = cong MkU $ vectorExtensionality (zipWith or bv1 bv2) (zipWith or bv2 bv1) f
    where
      f : (i : _) -> index i (zipWith B.or bv1 bv2) = index i (zipWith B.or bv2 bv1)
      f i = zipWithIndexLinear or bv1 bv2 i `trans`
            B.orCommutes _ _                `trans`
            sym (zipWithIndexLinear or bv2 bv1 i)

  orRightId (MkU bv) = cong MkU $ vectorExtensionality (zipWith or bv Zeros) bv f
    where
      f : (i : _) -> index i (zipWith B.or bv Zeros) = index i bv
      f i = zipWithIndexLinear or bv Zeros i `trans`
            rewrite indexReplicate i O in B.orRightId _

  orRightOne (MkU bv) = cong MkU $ vectorExtensionality (zipWith or bv Ones) Ones f
    where
      f : (i : _) -> index i (zipWith B.or bv Ones) = index i Ones
      f i = zipWithIndexLinear or bv Ones i `trans`
            rewrite indexReplicate i I in B.orRightOne _

  orRightLess (MkU bv1) (MkU bv2) = lteHomo _ _ (bvLteOrRight _ _)


  complementInvolutive (MkU bv) = rewrite mapFusion not not bv in
                                  rewrite mapExtensional (B.not . B.not) id notInvolutive bv in
                                          cong MkU $ mapId bv


  shiftLZero (MkU bv) with (splitLAtFin FZ bv)
    shiftLZero (MkU ([] ++ after)) | TheSplit {n2 = S n} [] after _ with (appendRightNeutral after)
      _ | eqPrf with (plusZeroRightNeutral n)
                   | (plus n Z)
        _ | Refl | _ = cong MkU eqPrf

  shiftRZero (MkU bv) with (splitRAtFin FZ bv)
    shiftRZero (MkU (before ++ [])) | TheSplit {n1 = S n} before [] _ with (appendRightNeutral before)
      _ | eqPrf with (plusZeroRightNeutral n)
                   | (plus n Z)
        _ | Refl | _ = cong MkU $ sym eqPrf

  shiftRBounded v s = rewrite toNumCorrelates (v `shiftR` s) in 
                      rewrite sym $ finToNatLastIsBound {n = bound $ natSubFin (S w) s} in
                              flteToLte $ shiftRBoundedImpl v s
    where
      toNumCorrelates : (ubv : UnsignedBV (S w)) ->
                        toNum ubv = finToNat (getFinVal $ bvToFin ubv)
      toNumCorrelates (MkU _) = Refl
