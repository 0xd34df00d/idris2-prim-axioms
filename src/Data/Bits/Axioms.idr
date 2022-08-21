module Data.Bits.Axioms

import Data.Fin
import Data.Nat
import Decidable.Equality

%default total

infixl 10 ^^

public export
(^^) : Num a => a -> Nat -> a
_ ^^ Z = 1
x ^^ (S y) = x * x ^^ y

export
powOneLeft : (k : _) -> (the Nat 1) ^^ k = 1
powOneLeft Z = Refl
powOneLeft (S k) = plusZeroRightNeutral (1 ^^ k) `trans` powOneLeft k

export
powNonNeg : (n, k : Nat) -> 0 `LT` S n ^^ k
powNonNeg n Z = LTESucc LTEZero
powNonNeg n (S k) = let r = powNonNeg n k
                     in ?powNonNeg_rhs_1

eqZeroNotPositive : n = 0 -> 0 `LT` n -> Void
eqZeroNotPositive Refl LTEZero impossible
eqZeroNotPositive Refl (LTESucc x) impossible

namespace Unsigned
  public export %inline
  bound : (w : Nat) -> Nat
  bound w = 2 ^^ w

  public export
  data Unsigned : (w : Nat) -> Type where
    MkU : (val : Fin (bound w)) -> Unsigned w

  DecEq (Unsigned w) where
    decEq (MkU val1) (MkU val2) = case decEq val1 val2 of
                                       Yes Refl => Yes Refl
                                       No contra => No $ \case Refl => contra Refl

  boundedFinNonEmpty : {w : _}
                    -> (val1, val2 : Fin (bound w))
                    -> ({n : _} -> Fin (S n) -> Fin (S n) -> Fin (S n))
                    -> Fin (bound w)
  boundedFinNonEmpty val1 val2 f with (bound w)
    _ | Z = absurd val1
    _ | S _ = f val1 val2

  {w : _} -> Num (Unsigned w) where
    MkU val1 + MkU val2 = MkU $ boundedFinNonEmpty val1 val2 (+)
    MkU val1 * MkU val2 = MkU $ boundedFinNonEmpty val1 val2 (*)
    fromInteger z with (bound w) proof p
      _ | Z = absurd $ eqZeroNotPositive p (powNonNeg 1 w)
      _ | S _ = MkU $ rewrite p in Num.fromInteger z
