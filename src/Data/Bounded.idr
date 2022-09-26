module Data.Bounded

import Data.Nat
import Data.Fin

import Data.Bits.NonEmpty

public export
data Bounded : (ty : Type) ->
               NonEmptyBits ty =>
               (0 n : Nat) ->
               Type where
  MkBounded : NonEmptyBits ty =>
              (v : ty) ->
              (0 prf : toNum v `LT` n) ->
              Bounded ty n

public export %inline
bValue : NonEmptyBits ty => Bounded ty n -> ty
bValue (MkBounded v _) = v


||| Given a value `v` and a proof that it's smaller than some natural `n`,
||| convert `v` to any `Fin` with a bound ≥ `n`.
export %inline
asFin : NonEmptyBits ty =>
        Bounded ty n ->
        Fin (n + m)
asFin (MkBounded v prf) = natToFinLT (toNum v) {prf = prf `transitive` lteAddRight n}

export
natToFinLtToNat : (x : Nat) ->
                  {0 n : Nat} ->
                  {auto 0 prf : x `LT` n} ->
                  finToNat (natToFinLT {n} x) = x
natToFinLtToNat Z {prf = LTESucc _} = Refl
natToFinLtToNat (S x) {prf = LTESucc _} = cong S $ natToFinLtToNat x

||| `asFin` preserves the numeric value of its argument.
export
asFinPreserves : NonEmptyBits ty =>
                 (bounded : Bounded ty n) ->
                 finToNat (asFin bounded) = toNum (bValue bounded)
asFinPreserves (MkBounded v prf) = natToFinLtToNat (toNum v) {prf = prf `transitive` lteAddRight n}
