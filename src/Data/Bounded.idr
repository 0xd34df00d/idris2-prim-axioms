module Data.Bounded

import Data.Nat
import Data.Fin

import Data.Bits.NonEmpty

public export
data Bounded : (ty : Type) ->
               (0 n : Nat) ->
               Type where
  MkBounded : NonEmptyBits ty =>
              (v : ty) ->
              (0 prf : toNum v `LT` n) ->
              Bounded ty n

public export %inline
bValue : NonEmptyBits ty => Bounded ty n -> ty
bValue (MkBounded v _) = v

public export %inline
negate : Neg ty => Bounded ty n -> ty
negate (MkBounded v _) = negate v
