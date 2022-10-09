import Data.Bits.Verified

import Data.Fin.Sub
import Data.Nat.Utils

%default total

pcg : (state : Bits64) -> (inc : Bits64) -> (Bits32, Bits64)
pcg state inc = let xorshifted = ((state .>>. 18) `xor` state) .>>. 27
                    out = xorshifted .>>. (state .>>.| 59)
                      .|. xorshifted .<<. (negate (state .>>. 59) .&.| 31)
                 in (cast out, state * 6364136223846793005 + inc)

main : IO ()
main = print $ pcg 2 2
