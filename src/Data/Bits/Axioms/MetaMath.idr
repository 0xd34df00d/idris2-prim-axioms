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

public export
natSubFin : (n : Nat) -> Fin n -> Nat
natSubFin (S n) FZ = S n
natSubFin (S n) (FS f) = natSubFin n f

export
natSubFinZero : (n : _)
             -> S n `natSubFin` FZ = S n
natSubFinZero n = Refl

export
natSubFinLast : (n : _)
             -> S n `natSubFin` last {n = n} = S Z
natSubFinLast Z = Refl
natSubFinLast (S n) = natSubFinLast n

-- TODO potentially move this out to base libs
[finToNatBound] (n : _) => (f : Fin n) => Uninhabited (n = finToNat f) where
  uninhabited {n = n} {f = f} = go n f
    where
      go : (n : _) -> (f : Fin n) -> Not (n = finToNat f)
      go Z f _ = uninhabited f
      go (S n) FZ prf = uninhabited prf
      go (S n) (FS f) prf = go n f (injective prf)

export
natSubFinPlus : (n1, n2 : Nat)
             -> (f : Fin (n1 + n2))
             -> n2 = finToNat f
             -> natSubFin (n1 + n2) f = n1
natSubFinPlus Z n2 f prf = absurd @{finToNatBound} prf
natSubFinPlus (S n1) _ FZ Refl = cong S $ plusZeroRightNeutral n1
natSubFinPlus (S n1) (S n2) (FS f) prf = let sEqPrf = plusSuccRightSucc n1 n2 in
                                         rewrite sym sEqPrf in
                                                 natSubFinPlus (S n1) n2 (rewrite sEqPrf in f) (injective prf)

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

infixl 1 `trans`

export
pointwisePlusRightCancel : (f1 : Fin m)
                        -> (f2 : Fin n)
                        -> (f : Fin (S _))
                        -> f1 + f ~~~ f2 + f
                        -> f1 ~~~ f2
pointwisePlusRightCancel f1 f2 f pw
  = let eq = sym (finToNatPlusHomo f1 f) `trans`
             finToNatQuotient pw         `trans`
             finToNatPlusHomo f2 f
        eq' = plusRightCancel _ _ _ eq
     in finToNatEqualityAsPointwise _ _ eq'

export
pointwisePlusRightCancel' : (f1, f2 : Fin m)
                         -> (f : Fin (S n))
                         -> f1 + f ~~~ f2 + f
                         -> f1 = f2
pointwisePlusRightCancel' f1 f2 f pw = homoPointwiseIsEqual $ pointwisePlusRightCancel f1 f2 f pw
