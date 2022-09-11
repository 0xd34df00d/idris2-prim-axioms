module Data.Bits.Verified.Prim

import Data.Bits as B

import Data.Bits.Axioms
import Data.Bits.Repr
import Data.Bits.Verified as R
import Data.Bits.Verified.Repr

%default total

export
-- TODO ideally we'd write smth like this, but idris is unhappy for now:
-- {w : _} -> (Bits prim, VerifiedBits (UnsignedBV w), IsModelOf (UnsignedBV w) prim) => VerifiedBits prim where
VerifiedBits Bits64 where
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
