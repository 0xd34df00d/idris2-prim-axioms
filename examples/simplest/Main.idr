import Data.Bits.Verified

import Data.Fin.Sub
import Data.Nat.Utils

%default total

ex : Bits8 -> Bits8
ex bs = let shift = bs .>>.| (the (Fin 8) 6)
         in bs `shiftR` shift

main : IO ()
main = do
  str <- getLine
  printLn $ ex $ cast str
