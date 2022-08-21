module Data.Bits.Axioms.MetaMath

import Data.Fin

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
powNonNeg : (n, k : Nat) -> 0 `LT` S n ^^ k
powNonNeg n Z = LTESucc LTEZero
powNonNeg n (S k) = let r = powNonNeg n k
                     in ltePlusLeft r

export
eqZeroNotPositive : n = 0 -> 0 `LT` n -> Void
eqZeroNotPositive Refl LTEZero impossible
eqZeroNotPositive Refl (LTESucc x) impossible
