module Data.Bits.Repr.Order

import Data.Vect

import Data.Bits.BitDef
import Data.Bits.Repr

%default total

data BvLTE : (l, r : Vect w Bit) -> Type where
  EmptyLTE  : BvLTE [] []
  HereLT    : (l, r : Vect w Bit)
           -> BvLTE (O :: l) (I :: r)
  ThereLTE  : BvLTE l r
           -> BvLTE (b :: l) (b :: r)

mutual
  bvLteThere : (l, r : _) -> Dec (b :: l `BvLTE` b :: r)
  bvLteThere l r = case isBvLTE l r of
                        Yes prf => Yes $ ThereLTE prf
                        No contra => No $ \case ThereLTE lte => contra lte

  isBvLTE : (l, r : _) -> Dec (l `BvLTE` r)
  isBvLTE [] [] = Yes EmptyLTE
  isBvLTE (O :: l) (O :: r) = bvLteThere l r
  isBvLTE (O :: l) (I :: r) = Yes $ HereLT l r
  isBvLTE (I :: l) (O :: r) = No $ \lte => case lte of
                                                EmptyLTE impossible
                                                HereLT _ _ impossible
                                                ThereLTE _ impossible
  isBvLTE (I :: l) (I :: r) = bvLteThere l r
