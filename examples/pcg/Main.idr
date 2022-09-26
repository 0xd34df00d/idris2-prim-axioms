import Data.Bits
import Data.Bits.Verified.Prim

import Data.Fin.Sub
import Data.Nat.Utils

%default total

pcg : (state : Bits64) -> (inc : Bits64) -> (Bits32, Bits64)
pcg state inc = let xorshifted = ((state .>>. 18) `xor` state) .>>. 27
                    rot = state .>>.| the (Fin 64) 59
                    out = cast $ (xorshifted .>>. rot) .|. (xorshifted .<<. negate rot)
                 in (out, state * 6364136223846793005 + inc)

main : IO ()
main = print $ pcg 2 2
