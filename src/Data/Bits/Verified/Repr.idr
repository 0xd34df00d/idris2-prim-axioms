module Data.Bits.Verified.Repr

import Data.Bits as B
import Data.Fin
import Data.Fin.Extra
import Data.Vect
import Data.Vect.Properties.Index
import Data.Vect.Properties.Tabulate

import Data.Bits.Axioms.MetaMath
import Data.Bits.BitDef as B
import Data.Bits.Repr
import Data.Bits.Verified
import Data.Fin.Order
import Data.Vect.Utils

%default total

accBVLeftZero : {w : _}
             -> (bv : Vect w Bit)
             -> accBV (O :: bv) ~~~ accBV bv
accBVLeftZero {w = w} bv with (plusZeroRightNeutral $ bound w)
                            | (bound w + Z)
  _ | Refl | _ = plusZeroRightNeutral (accBV bv)

zeroPaddedBound : {n : _}
               -> (m : _)
               -> (right : Vect n Bit)
               -> accBV (replicate m O ++ right) `FLTE` last' (bound n)
zeroPaddedBound Z right = lastIsLast (accBV right)
zeroPaddedBound (S m) right = let pw = symmetric $ accBVLeftZero (replicate m O ++ right)
                               in fltePointwiseLeft _ _ pw (zeroPaddedBound m right)

shiftRBoundedImpl : {w : _}
                 -> (v : UnsignedBV w)
                 -> (s : Fin w)
                 -> getFinVal (bvToFin (v `shiftR` s)) `FLTE` last' (bound $ w `natSubFin` s)
shiftRBoundedImpl (MkU bv) s with (splitRAtFin s bv)
  shiftRBoundedImpl (MkU _) s | TheSplit {n1 = n1, n2 = n2} before after eq
                                = rewrite natSubFinPlus n1 n2 s eq in
                                  rewrite plusCommutative n1 n2 in
                                          zeroPaddedBound n2 before

export
{w : _} -> VerifiedBits (UnsignedBV (S w)) where
  toNum (MkU bv) = accBV bv

  andCommutes (MkU bv1) (MkU bv2) = cong MkU $ vectorExtensionality (zipWith and bv1 bv2) (zipWith and bv2 bv1) f
    where
      f : (i : _) -> index i (zipWith B.and bv1 bv2) = index i (zipWith B.and bv2 bv1)
      f i = zipWithIndexLinear and bv1 bv2 i `trans`
            B.andCommutes _ _                `trans`
            sym (zipWithIndexLinear and bv2 bv1 i)

  andRightId (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv (replicate _ I)) bv f
    where
      f : (i : _) -> index i (zipWith B.and bv (replicate _ I)) = index i bv
      f i = zipWithIndexLinear and bv (replicate _ I) i `trans`
            rewrite indexReplicate i I in B.andRightId _

  andRightZero (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv (replicate _ O)) (replicate _ O) f
    where
      f : (i : _) -> index i (zipWith B.and bv (replicate _ O)) = index i (replicate _ O)
      f i = zipWithIndexLinear and bv (replicate _ O) i `trans`
            rewrite indexReplicate i O in B.andRightZero _

  orRightId (MkU bv) = cong MkU $ vectorExtensionality (zipWith or bv (replicate _ O)) bv f
    where
      f : (i : _) -> index i (zipWith B.or bv (replicate _ O)) = index i bv
      f i = zipWithIndexLinear or bv (replicate _ O) i `trans`
            rewrite indexReplicate i O in B.orRightId _

  orLeftId (MkU bv) = cong MkU $ vectorExtensionality (zipWith or (replicate _ O) bv) bv f
    where
      f : (i : _) -> index i (zipWith B.or (replicate _ O) bv) = index i bv
      f i = zipWithIndexLinear or (replicate _ O) bv i `trans`
            rewrite indexReplicate i O in B.orLeftId _

  zeroIndex = FZ
  zeroIndexIsZero = Refl

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
                              shiftRBoundedImpl v s
    where
      toNumCorrelates : (ubv : UnsignedBV (S w))
                     -> toNum ubv = getFinVal (bvToFin ubv)
      toNumCorrelates (MkU _) = Refl
