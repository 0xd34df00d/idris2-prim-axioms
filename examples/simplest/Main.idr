import Data.Bits
import Data.Bits.Verified.Prim

import Data.Fin.Sub
import Data.Nat.Utils

%default total

ex : Bits8 -> Bits8
ex bs = let (shift ** prf) = bs .>>.** 6
            shift' = natToFinLT (cast shift) {prf = prf `transitive` %search}
         in bs `shiftR` shift'

main : IO ()
main = do
  str <- getLine
  printLn $ ex $ cast str
