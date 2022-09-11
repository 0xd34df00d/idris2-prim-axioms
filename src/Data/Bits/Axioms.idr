module Data.Bits.Axioms

import Data.Bits as B

import Data.Bits.Repr
import Data.Bits.Verified
import Data.Bits.Verified.Repr

%default total

export
interface (Bits prim, Bits repr) => IsModelOf repr prim | prim where
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

  prim2reprInjective : {0 v1, v2 : prim}
                    -> prim2repr v1 = prim2repr v2
                    -> v1 = v2
  prim2reprInjective = believe_me ()

export IsModelOf (UnsignedBV 8)  Bits8  where
export IsModelOf (UnsignedBV 16) Bits16 where
export IsModelOf (UnsignedBV 32) Bits32 where
export IsModelOf (UnsignedBV 64) Bits64 where
