module Data.Bits.Repr.Order

import Data.Fin
import Data.Fin.Extra
import Data.Fin.Order
import Data.Vect

import Data.Bits.BitDef as B
import Data.Bits.Repr
import Data.Nat.Utils

%default total

public export
data BvLTE : (l, r : Vect w Bit) -> Type where
  EmptyLTE  : BvLTE [] []
  HereLT    : BvLTE (O :: l) (I :: r)
  ThereLTE  : BvLTE l r ->
              BvLTE (b :: l) (b :: r)

%name BvLTE bvLTE

mutual
  bvLteThere : (l, r : _) ->
               Dec (b :: l `BvLTE` b :: r)
  bvLteThere l r = case isBvLTE l r of
                        Yes prf => Yes $ ThereLTE prf
                        No contra => No $ \case ThereLTE lte => contra lte

  export
  isBvLTE : (l, r : _) ->
            Dec (l `BvLTE` r)
  isBvLTE [] [] = Yes EmptyLTE
  isBvLTE (O :: l) (O :: r) = bvLteThere l r
  isBvLTE (O :: l) (I :: r) = Yes HereLT
  isBvLTE (I :: l) (O :: r) = No $ \lte => case lte of
                                                EmptyLTE impossible
                                                HereLT impossible
                                                ThereLTE _ impossible
  isBvLTE (I :: l) (I :: r) = bvLteThere l r


export
flteHomo : {w : _} ->
           (l, r : Vect w Bit) ->
           l `BvLTE` r ->
           accBV l `FLTE` accBV r
flteHomo _ _ EmptyLTE = FLTEZero
flteHomo {w = S w} (_ :: l) (_ :: r) HereLT with (plusZeroRightNeutral $ bound w)
                                               | (bound w + Z)
  _ | Refl | _ = fltePointwiseLeft (symmetric $ plusZeroRightNeutral $ accBV l)
               $ lastIsLast (accBV l) `flteTrans` fltePlusLeft _ _
flteHomo {w = S w} (_ :: l) (_ :: r) (ThereLTE bvLTE) with (plusZeroRightNeutral $ bound w)
                                                        | (bound w + Z)
  _ | Refl | _ = fltePlusBoth $ flteHomo _ _ bvLTE

export
lteHomo : {w : _} ->
          (l, r : Vect w Bit) ->
          l `BvLTE` r ->
          finToNat (accBV l) `LTE` finToNat (accBV r)
lteHomo l r bvLTE = flteToLte $ flteHomo l r bvLTE


export
bvLteAndRight : (v1, v2 : Vect w Bit) ->
                zipWith B.and v1 v2 `BvLTE` v2
bvLteAndRight [] [] = EmptyLTE
bvLteAndRight (O :: v1) (O :: v2) = ThereLTE (bvLteAndRight v1 v2)
bvLteAndRight (O :: v1) (I :: v2) = HereLT
bvLteAndRight (I :: v1) (O :: v2) = ThereLTE (bvLteAndRight v1 v2)
bvLteAndRight (I :: v1) (I :: v2) = ThereLTE (bvLteAndRight v1 v2)

export
bvLteOrRight : (v1, v2 : Vect w Bit) ->
               v2 `BvLTE` zipWith B.or v1 v2
bvLteOrRight [] [] = EmptyLTE
bvLteOrRight (O :: v1) (O :: v2) = ThereLTE (bvLteOrRight v1 v2)
bvLteOrRight (O :: v1) (I :: v2) = ThereLTE (bvLteOrRight v1 v2)
bvLteOrRight (I :: v1) (O :: v2) = HereLT
bvLteOrRight (I :: v1) (I :: v2) = ThereLTE (bvLteOrRight v1 v2)
