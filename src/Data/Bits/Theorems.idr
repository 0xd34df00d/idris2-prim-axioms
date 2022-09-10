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
andRightId {w} (MkU bv) = cong MkU $ pointwiseEq (zipWith and bv (replicate w I)) bv f
  where
    f : (i : Fin _) -> index i (zipWith B.and bv (replicate w I)) = index i bv
    f i = zipWithIndexLinear and bv (replicate w I) i `trans`
          rewrite anyIndexOfReplicate w I i in B.andRightId _

export
andLeftId : {w : _}
         -> (bv : UnsignedBV w)
         -> B.oneBits .&. bv = bv
andLeftId {w} (MkU bv) = cong MkU $ pointwiseEq (zipWith and (replicate w I) bv) bv f
  where
    f : (i : Fin _) -> index i (zipWith B.and (replicate w I) bv) = index i bv
    f i = zipWithIndexLinear and (replicate w I) bv i `trans`
          rewrite anyIndexOfReplicate w I i in B.andLeftId _
