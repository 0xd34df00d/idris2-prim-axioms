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
data FLTE : (fm : Fin m) -> (fn : Fin n) -> Type where
  FLTEZero : FZ `FLTE` fn
  FLTESucc : fm `FLTE` fn -> FS fm `FLTE` FS fn

public export
FLT : (fm : Fin m) -> (fn : Fin n) -> Type
FLT fm fn = FS fm `FLTE` fn

export
Uninhabited (FS fm `FLTE` FZ) where
  uninhabited FLTEZero impossible
  uninhabited (FLTESucc x) impossible

export
isFLTE : (fm : Fin m) -> (fn : Fin n) -> Dec (fm `FLTE` fn)
isFLTE FZ fn = Yes FLTEZero
isFLTE (FS fm) FZ = No uninhabited
isFLTE (FS fm) (FS fn) = case fm `isFLTE` fn of
                              Yes prf => Yes (FLTESucc prf)
                              No contra => No $ \case FLTESucc prf => contra prf

export
isFLT : (fm : Fin m) -> (fn : Fin n) -> Dec (fm `FLT` fn)
isFLT fm fn = FS fm `isFLTE` fn

export
flteInv : fm `FLTE` fn -> Not (fn `FLT` fm)
flteInv FLTEZero flt = uninhabited flt
flteInv (FLTESucc flte) (FLTESucc flt) = flteInv flte flt

decidableDN : Dec prop -> Not (Not prop) -> prop
decidableDN (Yes prf) notNot = prf
decidableDN (No contra) notNot = absurd (notNot contra)

export
flteInvNot : {fm : Fin m}
          -> {fn : Fin n}
          -> Not (fm `FLTE` fn)
          -> fn `FLT` fm
flteInvNot {fm = FZ} {fn} contra = absurd $ contra FLTEZero
flteInvNot {fm = FS fm} {fn = FZ} contra = FLTESucc FLTEZero
flteInvNot {fm = FS fm} {fn = FS fn} contra = FLTESucc (flteInvNot (\x => contra (FLTESucc x)))

export
fltInvNot : {fm : Fin m}
         -> {fn : Fin n}
         -> Not (fm `FLT` fn)
         -> fn `FLTE` fm
fltInvNot contra = case flteInvNot contra of FLTESucc x => x
