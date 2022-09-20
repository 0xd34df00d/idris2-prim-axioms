module Data.Bits.Repr.Order

import Data.Fin
import Data.Fin.Extra
import Data.Fin.Order
import Data.Vect

import Data.Bits.Axioms.MetaMath
import Data.Bits.BitDef
import Data.Bits.Repr

%default total

data BvLTE : (l, r : Vect w Bit) -> Type where
  EmptyLTE  : BvLTE [] []
  HereLT    : BvLTE (O :: l) (I :: r)
  ThereLTE  : BvLTE l r
           -> BvLTE (b :: l) (b :: r)

%name BvLTE bvLTE

mutual
  bvLteThere : (l, r : _) -> Dec (b :: l `BvLTE` b :: r)
  bvLteThere l r = case isBvLTE l r of
                        Yes prf => Yes $ ThereLTE prf
                        No contra => No $ \case ThereLTE lte => contra lte

  isBvLTE : (l, r : _) -> Dec (l `BvLTE` r)
  isBvLTE [] [] = Yes EmptyLTE
  isBvLTE (O :: l) (O :: r) = bvLteThere l r
  isBvLTE (O :: l) (I :: r) = Yes HereLT
  isBvLTE (I :: l) (O :: r) = No $ \lte => case lte of
                                                EmptyLTE impossible
                                                HereLT impossible
                                                ThereLTE _ impossible
  isBvLTE (I :: l) (I :: r) = bvLteThere l r


lteHomo : {w : _}
       -> (l, r : Vect w Bit)
       -> l `BvLTE` r
       -> accBV l `FLTE` accBV r
lteHomo _ _ EmptyLTE = FLTEZero
lteHomo {w = S w} (_ :: l) (_ :: r) HereLT with (plusZeroRightNeutral $ bound w)
                                              | (bound w + Z)
  _ | Refl | _ = let rec = lastIsLast (accBV l) in
                 fltePointwiseLeft _ _ (symmetric $ plusZeroRightNeutral $ accBV l)
               $ lastIsLast (accBV l) `flteTrans` fltePlusLeft _ _
lteHomo {w = S w} (_ :: l) (_ :: r) (ThereLTE bvLTE) with (plusZeroRightNeutral $ bound w)
                                                        | (bound w + Z)
  _ | Refl | _ = fltePlusBoth $ lteHomo _ _ bvLTE
