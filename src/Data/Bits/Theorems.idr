module Data.Bits.Theorems

import Data.Bits as B
import Data.Fin
import Data.Vect

import Data.Bits.Axioms
import Data.Bits.BitDef as B
import Data.Vect.Utils

%default total

export
andRightId : {w : _}
          -> (bv : UnsignedBV w)
          -> bv .&. B.oneBits = bv
andRightId (MkU bv) = cong MkU $ pointwiseEq (zipWith and bv (replicate _ I)) bv f
  where
    f : (i : _) -> index i (zipWith B.and bv (replicate _ I)) = index i bv
    f i = zipWithIndexLinear and bv (replicate w I) i `trans`
          rewrite anyIndexOfReplicate w I i in B.andRightId _

export
andLeftId : {w : _}
         -> (bv : UnsignedBV w)
         -> B.oneBits .&. bv = bv
andLeftId (MkU bv) = cong MkU $ pointwiseEq (zipWith and (replicate _ I) bv) bv f
  where
    f : (i : _) -> index i (zipWith B.and (replicate _ I) bv) = index i bv
    f i = zipWithIndexLinear and (replicate w I) bv i `trans`
          rewrite anyIndexOfReplicate w I i in B.andLeftId _

export
andCommutes : (bv1, bv2 : UnsignedBV w)
           -> bv1 .&. bv2 = bv2 .&. bv1
andCommutes (MkU bv1) (MkU bv2) = cong MkU $ pointwiseEq (zipWith and bv1 bv2) (zipWith and bv2 bv1) f
  where
    f : (i : _) -> index i (zipWith B.and bv1 bv2) = index i (zipWith B.and bv2 bv1)
    f i = zipWithIndexLinear and bv1 bv2 i `trans`
          B.andCommutes _ _                `trans`
          sym (zipWithIndexLinear and bv2 bv1 i)
