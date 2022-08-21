module Data.Bits.Axioms

import Data.Fin
import Data.Nat
import Decidable.Equality

import Data.Bits.Axioms.MetaMath

%default total

namespace Unsigned
  public export %inline
  bound : (1 w : Nat) -> Nat
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
