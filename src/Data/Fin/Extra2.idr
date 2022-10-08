module Data.Fin.Extra2

import Data.Fin

%default total

export
natToFinLtToNat : (x : Nat) ->
                  {0 n : Nat} ->
                  {auto 0 prf : x `LT` n} ->
                  finToNat (natToFinLT {n} x) = x
natToFinLtToNat Z {prf = LTESucc _} = Refl
natToFinLtToNat (S x) {prf = LTESucc _} = cong S $ natToFinLtToNat x
