module Data.Nat.Utils

import Data.Nat

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
ltePlusLeft a≤b = rewrite sym $ plusZeroRightNeutral a in plusLteMonotone a≤b LTEZero

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
