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

export
natToFinLtToNat : (x : Nat) ->
                  {0 n : Nat} ->
                  {auto 0 prf : x `LT` n} ->
                  finToNat (natToFinLT {n} x) = x
natToFinLtToNat Z {prf = LTESucc _} = Refl
natToFinLtToNat (S x) {prf = LTESucc _} = cong S $ natToFinLtToNat x
