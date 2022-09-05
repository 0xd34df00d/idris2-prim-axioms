module Data.Bits.Axioms

import Data.Bits
import Data.Fin as F
import Data.Fin.Extra
import Data.Nat
import Data.Vect
import Decidable.Equality

import Data.Bits.Axioms.MetaMath
import Data.Bits.BitDef
import Data.Fin.Order

%default total

namespace AsFin
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
      _ | Z = absurd $ eqZeroNotPositive p (powPositive 1 w)
      _ | S _ = MkU $ rewrite p in Num.fromInteger z

namespace AsBV
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
  finToFactors {w = Z} FZ = []
  finToFactors {w = S w} f with (f `minusF` bound w)
    _ | MinuendSmaller smaller = let f = strengthenFLT _ _ smaller
                                  in O :: finToFactors f
    _ | MDifference diff _ = let p = plusMinusZero (bound w) (bound w)
                                 diff = replace {p = Fin} p diff
                              in I :: finToFactors diff

  export
  finToBV : {w : _} -> UnsignedF w -> UnsignedBV w
  finToBV (MkU val) = MkU $ finToFactors val

  export
  accBV : {w : _} -> Vect w Bit -> Fin (bound w)
  accBV {w = Z} [] = FZ
  accBV {w = S w} (b :: bs) with (plusZeroRightNeutral $ bound w)
                               | (bound w + Z)
    _ | Refl | _ = accBV bs + bitToVal w b

  export
  bvToFin : {w : _} -> UnsignedBV w -> UnsignedF w
  bvToFin (MkU bv) = MkU $ accBV bv

  export
  isoFtoBVtoF : {w : _} -> (f : Fin (bound w)) -> accBV (finToFactors {w} f) = f
  isoFtoBVtoF {w = Z} FZ = Refl
  isoFtoBVtoF {w = S w} f with (f `minusF` bound w)
    _ | MinuendSmaller smaller with (plusZeroRightNeutral $ bound w)
                                  | (bound w + Z)
      _ | Refl | _ = rewrite isoFtoBVtoF {w} (strengthenFLT _ _ smaller) in
                             strengthenFLTPlusFZ f last smaller
    _ | MDifference diff eq with (plusZeroRightNeutral $ bound w)
                               | (bound w + Z)
      _ | Refl | _ with (minusPlus {n = bound w} (bound w))
                      | ((bound w + bound w) `minus` bound w)
        _ | Refl | _ = rewrite isoFtoBVtoF {w} diff in
                               hetPointwiseIsTransport Refl eq

  export
  isoBVtoFtoBV : {w : _} -> (bv : Vect w Bit) -> finToFactors {w} (accBV bv) = bv
  isoBVtoFtoBV {w = Z} [] = Refl
  isoBVtoFtoBV {w = S w} (b :: bv) with (plusZeroRightNeutral $ bound w)
                                      | (bound w + Z)
    _ | Refl | _ with ((accBV bv + bitToVal w b) `minusF` bound w)
      _ | MinuendSmaller smaller
          = case b of
                 O => let rec = isoBVtoFtoBV bv
                          step = cong finToFactors
                               $ sym
                               $ homoPointwiseIsEqual
                               $ symmetric (plusZeroRightNeutral $ accBV bv) `transitive`
                                 strengthenFLTPreserves (accBV bv + FZ) last smaller
                       in cong (O ::) $ rewrite plusZeroRightNeutral (bound w) in step `trans` rec
                 I => absurd $ flteInv (fltePlusLeft _ _) smaller
      _ | MDifference diff eq with (minusPlus {n = bound w} (bound w))
                                 | ((bound w + bound w) `minus` bound w)
        _ | Refl | _
            = case b of
                   O => let eq' = eq `F.Equality.transitive` plusZeroRightNeutral (accBV bv)
                         in absurd $ pointwisePlusLastAbsurd _ _ eq'
                   I => let eq' = cong finToFactors $ pointwisePlusRightCancel' _ _ _ eq
                            rec = isoBVtoFtoBV bv
                         in cong (I ::) $ eq' `trans` rec
