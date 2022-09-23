module Data.Fin.Pointwise.Extra

import Data.Fin
import Data.Fin.Extra

%default total

export
pointwisePlusLastAbsurd : {n : Nat} ->
                          (f1, f2 : Fin n) ->
                          Not (f1 + last {n = n} ~~~ f2)
pointwisePlusLastAbsurd f1 f2 eq
  = let natEq = sym (finToNatPlusHomo f1 last) `trans` finToNatQuotient eq
        lte = replace {p = LTE (S (finToNat f2))} (sym finToNatLastIsBound) (elemSmallerThanBound f2)
     in helper lte natEq
  where
    helper : {n1, n : _}
          -> n2 `LT` n
          -> Not (n1 + n = n2)
    helper n2lt Refl = let prf' = plusLteMonotone LTEZero reflexive
                        in LTEImpliesNotGT prf' n2lt

infixl 1 `trans`

export
pointwisePlusRightCancel : (f1 : Fin m) ->
                           (f2 : Fin n) ->
                           (f : Fin (S _)) ->
                           f1 + f ~~~ f2 + f ->
                           f1 ~~~ f2
pointwisePlusRightCancel f1 f2 f pw
  = let eq = sym (finToNatPlusHomo f1 f) `trans`
             finToNatQuotient pw         `trans`
             finToNatPlusHomo f2 f
        eq' = plusRightCancel _ _ _ eq
     in finToNatEqualityAsPointwise _ _ eq'

export
pointwisePlusRightCancel' : (f1, f2 : Fin m) ->
                            (f : Fin (S n)) ->
                            f1 + f ~~~ f2 + f ->
                            f1 = f2
pointwisePlusRightCancel' f1 f2 f pw = homoPointwiseIsEqual $ pointwisePlusRightCancel f1 f2 f pw
