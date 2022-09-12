module Data.Bits.Verified

import Data.Bits as B

%default total

public export
interface FiniteBits ty => VerifiedBits ty where
  andRightId   : (v : ty)
              -> v .&. B.oneBits = v
  andLeftId    : (v : ty)
              -> B.oneBits .&. v = v
  andRightZero : (v : ty)
              -> v .&. B.zeroBits = B.zeroBits
  andLeftZero  : (v : ty)
              -> B.zeroBits .&. v = B.zeroBits
  andCommutes  : (v1, v2 : ty)
              -> v1 .&. v2 = v2 .&. v1

  bitSizePred : Nat
  bitSizeCorrelates : S bitSizePred = bitSize {a = ty}

  bitsToIndex' : Fin (S bitSizePred) -> Index {a = ty}
  bitsToIndex' fin = bitsToIndex {a = ty} $ replace {p = Fin} bitSizeCorrelates fin
