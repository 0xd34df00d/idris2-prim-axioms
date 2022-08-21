module Data.Bits.Axioms

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Vect
import Decidable.Equality

import Data.Bits.Axioms.MetaMath

%default total

namespace AsFin
  public export %inline
  bound : (1 w : Nat) -> Nat
  bound w = 2 ^^ w

  public export
  data UnsignedF : (w : Nat) -> Type where
    MkU : (val : Fin (bound w)) -> UnsignedF w

  public export
  DecEq (UnsignedF w) where
    decEq (MkU val1) (MkU val2) = case decEq val1 val2 of
                                       Yes Refl => Yes Refl
                                       No contra => No $ \case Refl => contra Refl

  public export
  boundedFinNonEmpty : {w : _}
                    -> (val1, val2 : Fin (bound w))
                    -> ({n : _} -> Fin (S n) -> Fin (S n) -> Fin (S n))
                    -> Fin (bound w)
  boundedFinNonEmpty val1 val2 f with (bound w)
    _ | Z = absurd val1
    _ | S _ = f val1 val2

  public export
  {w : _} -> Num (UnsignedF w) where
    MkU val1 + MkU val2 = MkU $ boundedFinNonEmpty val1 val2 (+)
    MkU val1 * MkU val2 = MkU $ boundedFinNonEmpty val1 val2 (*)
    fromInteger z with (bound w) proof p
      _ | Z = absurd $ eqZeroNotPositive p (powNonNeg 1 w)
      _ | S _ = MkU $ rewrite p in Num.fromInteger z

namespace AsBV
  public export
  data Bit = O | I

  public export
  DecEq Bit where
    decEq I I = Yes Refl
    decEq I O = No $ \case Refl impossible
    decEq O I = No $ \case Refl impossible
    decEq O O = Yes Refl

  public export
  data UnsignedBV : (w : Nat) -> Type where
    MkU : (bv : Vect w Bit) -> UnsignedBV w

  public export
  DecEq (UnsignedBV w) where
    decEq (MkU b1) (MkU b2) = case decEq b1 b2 of
                                   Yes Refl => Yes Refl
                                   No contra => No $ \case Refl => contra Refl

namespace FisoBV
  bitToVal : (w : _) -> Bit -> Fin (S (bound w))
  bitToVal _ O = FZ
  bitToVal _ I = last

  export
  finToFactors : {w : _} -> Fin (bound w) -> Vect w Bit
  finToFactors {w = Z} _ = []
  finToFactors {w = S w} fin = ?w

  export
  finToBV : {w : _} -> UnsignedF w -> UnsignedBV w
  finToBV (MkU val) = MkU $ finToFactors val

  export
  accBV : {w : _} -> Vect w Bit -> Fin (bound w)
  accBV {w = Z} [] = FZ
  accBV {w = S w} (b :: bs) = let rec = accBV bs
                                  b' = bitToVal w b
                               in rewrite plusZeroRightNeutral (bound w)
                               in rec + b'

  export
  bvToFin : {w : _} -> UnsignedBV w -> UnsignedF w
  bvToFin (MkU bv) = MkU $ accBV bv
