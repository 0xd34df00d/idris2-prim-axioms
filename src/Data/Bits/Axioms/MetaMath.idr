module Data.Bits.Axioms.MetaMath

import Data.Fin
import Data.Fin.Extra

%default total

infixl 10 ^^

public export
(^^) : Num a => a -> (1 _ : Nat) -> a
_ ^^ Z = 1
x ^^ (S y) = x * x ^^ y

export
powOneLeft : (k : _) -> (the Nat 1) ^^ k = 1
powOneLeft Z = Refl
powOneLeft (S k) = plusZeroRightNeutral (1 ^^ k) `trans` powOneLeft k

%hint
ltePlusLeft : {a, b, c : _}
           -> a `LTE` b
           -> a `LTE` b + c
ltePlusLeft {a} a≤b = rewrite sym $ plusZeroRightNeutral a in plusLteMonotone a≤b LTEZero

export
powPositive : (n, k : Nat) -> Z `LT` S n ^^ k
powPositive n Z = LTESucc LTEZero
powPositive n (S k) = ltePlusLeft $ powPositive n k

export
eqZeroNotPositive : n = Z -> Z `LT` n -> Void
eqZeroNotPositive Refl LTEZero impossible
eqZeroNotPositive Refl (LTESucc x) impossible

export
plusMinusZero : (a, b : _) -> (a + (b + Z)) `minus` a = b
plusMinusZero _ b = rewrite plusZeroRightNeutral b in minusPlus _


public export %inline
bound : (1 w : Nat) -> Nat
bound w = 2 ^^ w


export
pointwisePlusLastAbsurd : {n : Nat}
                       -> (f1, f2 : Fin n)
                       -> Not (f1 + last {n = n} ~~~ f2)
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

export
finToNatEqualityAsPointwise : (fm : Fin m)
                           -> (fn : Fin n)
                           -> finToNat fm = finToNat fn
                           -> fm ~~~ fn
finToNatEqualityAsPointwise FZ FZ _ = FZ
finToNatEqualityAsPointwise FZ (FS fn) prf = absurd prf
finToNatEqualityAsPointwise (FS fm) FZ prf = absurd prf
finToNatEqualityAsPointwise (FS fm) (FS fn) prf = FS $ finToNatEqualityAsPointwise fm fn (injective prf)
