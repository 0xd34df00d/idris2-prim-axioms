module Data.Fin.Order

import Data.Fin
import Data.Fin.Extra

%default total

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

-- If m > n and (fm : Fin m) < (fn : Fin (S n)),
-- then fm could be strengthened to have the bound n.
export
strengthenFLT : {n : _}
             -> (fm : Fin m)
             -> (fn : Fin (S n))
             -> fm `FLT` fn
             -> Fin n
strengthenFLT {n = Z} _ (FS fn) _ = absurd fn
strengthenFLT {n = S n} FZ (FS fn) (FLTESucc flt) = FZ
strengthenFLT {n = S n} (FS fm) (FS fn) (FLTESucc flt) = FS $ strengthenFLT fm fn flt

-- `strengthenFLT` indeed doesn't change the value of the Fin.
export
strengthenFLTPreserves : {n : _}
                      -> (fm : Fin m)
                      -> (fn : Fin (S n))
                      -> (flt : fm `FLT` fn)
                      -> fm ~~~ strengthenFLT fm fn flt
strengthenFLTPreserves {n = Z} _ (FS fn) _ = absurd fn
strengthenFLTPreserves {n = S n} FZ (FS fn) (FLTESucc flt) = FZ
strengthenFLTPreserves {n = S n} (FS fm) (FS fn) (FLTESucc flt) = FS $ strengthenFLTPreserves fm fn flt

export
strengthenFLTPlusFZ : {m, n : _}
                   -> (fm : Fin (n + m))
                   -> (fn : Fin (S n))
                   -> (flt : fm `FLT` fn)
                   -> strengthenFLT fm fn flt + FZ {k = m} = fm
strengthenFLTPlusFZ {n = Z} _ (FS fn) _ = absurd fn
strengthenFLTPlusFZ {n = S n} FZ (FS fn) (FLTESucc flt) = Refl
strengthenFLTPlusFZ {n = S n} (FS fm) (FS fn) (FLTESucc flt) = cong FS $ strengthenFLTPlusFZ fm fn flt

export
flteInv : fm `FLTE` fn -> Not (fn `FLT` fm)
flteInv FLTEZero flt = uninhabited flt
flteInv (FLTESucc flte) (FLTESucc flt) = flteInv flte flt

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

public export %inline
last' : (n : _) -> Fin (S n)
last' _ = last

-- The result of subtracting `last : Fin (S m)` from `fn : Fin n`.
--
-- The reason for passing `n : Nat` and subtracting `last` is that
-- this way it's much easier to put the proper bound on the value
-- of the resulting `Fin` if the subtraction is successful.
public export
data Minus : (fn : Fin n) -> (m : Nat) -> Type where
  MinuendSmaller : (smaller : fn `FLT` last' m)
                -> fn `Minus` m
  MDifference : {n : Nat}
             -> {fn : Fin n}
             -> (difference : Fin (n `minus` m))
             -> (diffCorrect : difference + last' m ~~~ fn)
             -> fn `Minus` m

export
minusFLTE : {m, n : Nat}
         -> (fn : Fin n)
         -> last' m `FLTE` fn
         -> fn `Minus` m
minusFLTE {m = Z} {n = Z} fn FLTEZero = MDifference {n = Z} fn (plusZeroRightNeutral _)
minusFLTE {m = Z} {n = S _} fn FLTEZero = MDifference {n = S _} fn (plusZeroRightNeutral _)
minusFLTE {m = S _} {n = S _} (FS fn) (FLTESucc flte) with (minusFLTE fn flte)
  _ | MinuendSmaller flt = absurd $ flteInv flte flt
  _ | MDifference {n = n} diff eq = let eq' = symmetric (plusSuccRightSucc _ _) `transitive` FS eq
                                     in MDifference {n = S n} diff eq'

export
minusF : {n : _} -> (fn : Fin n) -> (m : Nat) -> fn `Minus` m
minusF fn m = case fn `isFLT` last' m of
                   Yes prf => MinuendSmaller prf
                   No contra => minusFLTE _ $ fltInvNot contra