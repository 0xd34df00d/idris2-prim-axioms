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
powNonNeg : (n, k : Nat) -> 0 `LT` S n ^^ k
powNonNeg n Z = LTESucc LTEZero
powNonNeg n (S k) = ltePlusLeft $ powNonNeg n k

export
eqZeroNotPositive : n = 0 -> 0 `LT` n -> Void
eqZeroNotPositive Refl LTEZero impossible
eqZeroNotPositive Refl (LTESucc x) impossible

public export %inline
bound : (1 w : Nat) -> Nat
bound w = 2 ^^ w

public export
(++) : {n, m : _} -> Fin n -> Fin (S m) -> Fin (n + m)
(++) = (+)

public export
finAddBounded : {w : _} -> Fin (bound w) -> Fin (bound w) -> Fin (bound (S w))
finAddBounded {w = w} f1 f2 with (bound w) proof p
  _ | Z = absurd f1
  _ | S n = rewrite plusZeroRightNeutral (S n) in
            rewrite sym $ plusSuccRightSucc n n in
            weaken $ f1 ++ f2

public export
finAddBoundedSucc : {w : _} -> Fin (bound w) -> Fin (bound w) -> Fin (bound (S w))
finAddBoundedSucc {w = w} f1 f2 with (bound w) proof p
  _ | Z = absurd f1
  _ | S n = rewrite plusZeroRightNeutral (S n) in
            rewrite sym $ plusSuccRightSucc n n in
            FS $ f1 ++ f2

public export
data FHalf : (w : Nat) -> Fin (bound w) -> Type where
  FHOdd  : (f : Fin (bound w)) -> FHalf (S w) (finAddBoundedSucc {w = w} f f)
  FHEven : (f : Fin (bound w)) -> FHalf (S w) (finAddBounded {w = w} f f)

public export
fhalf : {w : Nat} -> (f : Fin (bound w)) -> FHalf w f
fhalf FZ = ?w
fhalf (FS f) with (fhalf f)
  fhalf (FS (FS (f ++ f))) | FHOdd f = let r = FHEven (FS f) in ?w2
  fhalf (FS (f ++ f)) | FHEven f = FHOdd f
