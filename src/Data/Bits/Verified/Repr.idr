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

export
accBVLeftZero : {w : _}
             -> (bv : Vect w Bit)
             -> accBV (O :: bv) ~~~ accBV bv
accBVLeftZero {w = w} bv with (plusZeroRightNeutral $ bound w)
                            | (bound w + Z)
  _ | Refl | _ = plusZeroRightNeutral (accBV bv)

export
zeroPaddedBound : {n : _}
               -> (m : _)
               -> (right : Vect n Bit)
               -> accBV (replicate m O ++ right) `FLTE` last' (bound n)
zeroPaddedBound Z right = lastIsLast (accBV right)
zeroPaddedBound (S m) right = let pw = symmetric $ accBVLeftZero (replicate m O ++ right)
                               in fltePointwiseLeft _ _ pw (zeroPaddedBound m right)


export
{w : _} -> VerifiedBits (UnsignedBV (S w)) where
  andRightId (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv (replicate _ I)) bv f
    where
      f : (i : _) -> index i (zipWith B.and bv (replicate _ I)) = index i bv
      f i = zipWithIndexLinear and bv (replicate _ I) i `trans`
            rewrite indexReplicate i I in B.andRightId _

  andLeftId (MkU bv) = cong MkU $ vectorExtensionality (zipWith and (replicate _ I) bv) bv f
    where
      f : (i : _) -> index i (zipWith B.and (replicate _ I) bv) = index i bv
      f i = zipWithIndexLinear and (replicate _ I) bv i `trans`
            rewrite indexReplicate i I in B.andLeftId _

  andCommutes (MkU bv1) (MkU bv2) = cong MkU $ vectorExtensionality (zipWith and bv1 bv2) (zipWith and bv2 bv1) f
    where
      f : (i : _) -> index i (zipWith B.and bv1 bv2) = index i (zipWith B.and bv2 bv1)
      f i = zipWithIndexLinear and bv1 bv2 i `trans`
            B.andCommutes _ _                `trans`
            sym (zipWithIndexLinear and bv2 bv1 i)

  andRightZero (MkU bv) = cong MkU $ vectorExtensionality (zipWith and bv (replicate _ O)) (replicate _ O) f
    where
      f : (i : _) -> index i (zipWith B.and bv (replicate _ O)) = index i (replicate _ O)
      f i = zipWithIndexLinear and bv (replicate _ O) i `trans`
            rewrite indexReplicate i O in B.andRightZero _

  andLeftZero (MkU bv) = cong MkU $ vectorExtensionality (zipWith and (replicate _ O) bv) (replicate _ O) f
    where
      f : (i : _) -> index i (zipWith B.and (replicate _ O) bv) = index i (replicate _ O)
      f i = zipWithIndexLinear and (replicate _ O) bv i `trans`
            rewrite indexReplicate i O in Refl

  bitSizePred = w
  bitSizeCorrelates = Refl

  bitsToIndex' = id

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
