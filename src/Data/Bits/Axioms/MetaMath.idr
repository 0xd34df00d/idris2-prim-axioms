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
ltePlusLeft : {a, b, c : _} ->
              a `LTE` b ->
              a `LTE` b + c
ltePlusLeft {a} a≤b = rewrite sym $ plusZeroRightNeutral a in plusLteMonotone a≤b LTEZero

export
powPositive : (n, k : Nat) ->
              Z `LT` S n ^^ k
powPositive n Z = LTESucc LTEZero
powPositive n (S k) = ltePlusLeft $ powPositive n k

export
eqZeroNotPositive : n = Z ->
                    Not (Z `LT` n)
eqZeroNotPositive Refl LTEZero impossible
eqZeroNotPositive Refl (LTESucc x) impossible

export
plusMinusZero : (a, b : _) ->
                (a + (b + Z)) `minus` a = b
plusMinusZero _ b = rewrite plusZeroRightNeutral b in minusPlus _


public export %inline
bound : (1 w : Nat) ->
        Nat
bound w = 2 ^^ w

public export
natSubFin : (n : Nat) ->
            Fin n ->
            Nat
natSubFin (S n) FZ = S n
natSubFin (S n) (FS f) = natSubFin n f

export
natSubFinZero : (n : _) ->
                S n `natSubFin` FZ = S n
natSubFinZero n = Refl

export
natSubFinLast : (n : _) ->
                S n `natSubFin` last {n = n} = S Z
natSubFinLast Z = Refl
natSubFinLast (S n) = natSubFinLast n

finIsNotBound : {n : _} ->
                {f : Fin n} ->
                Not (n = finToNat f)
finIsNotBound {n = n} {f = f} = go n f
  where
    go : (n : _) -> (f : Fin n) -> Not (n = finToNat f)
    go Z f _ = uninhabited f
    go (S n) FZ prf = uninhabited prf
    go (S n) (FS f) prf = go n f (injective prf)

export
natSubFinPlus : (n1, n2 : Nat) ->
                (f : Fin (n1 + n2)) ->
                n2 = finToNat f ->
                natSubFin (n1 + n2) f = n1
natSubFinPlus Z n2 f prf = void $ finIsNotBound prf
natSubFinPlus (S n1) _ FZ Refl = cong S $ plusZeroRightNeutral n1
natSubFinPlus (S n1) (S n2) (FS f) prf = let sEqPrf = plusSuccRightSucc n1 n2 in
                                         rewrite sym sEqPrf in
                                                 natSubFinPlus (S n1) n2 (rewrite sEqPrf in f) (injective prf)
