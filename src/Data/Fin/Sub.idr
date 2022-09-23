module Data.Fin.Sub

import Data.Fin

%default total

public export
natSubFin : (n : Nat) ->
            Fin n ->
            Nat
natSubFin (S n) FZ = S n
natSubFin (S n) (FS f) = natSubFin n f

export
natSubFinZero : (n : _) ->
                S n `natSubFin` FZ = S n
natSubFinZero n = Refl

export
natSubFinLast : (n : _) ->
                S n `natSubFin` last {n = n} = S Z
natSubFinLast Z = Refl
natSubFinLast (S n) = natSubFinLast n

finIsNotBound : {n : _} ->
                {f : Fin n} ->
                Not (n = finToNat f)
finIsNotBound {n = n} {f = f} = go n f
  where
    go : (n : _) -> (f : Fin n) -> Not (n = finToNat f)
    go Z f _ = uninhabited f
    go (S n) FZ prf = uninhabited prf
    go (S n) (FS f) prf = go n f (injective prf)

export
natSubFinPlus : (n1, n2 : Nat) ->
                (f : Fin (n1 + n2)) ->
                n2 = finToNat f ->
                natSubFin (n1 + n2) f = n1
natSubFinPlus Z n2 f prf = void $ finIsNotBound prf
natSubFinPlus (S n1) _ FZ Refl = cong S $ plusZeroRightNeutral n1
natSubFinPlus (S n1) (S n2) (FS f) prf = let sEqPrf = plusSuccRightSucc n1 n2 in
                                         rewrite sym sEqPrf in
                                                 natSubFinPlus (S n1) n2 (rewrite sEqPrf in f) (injective prf)
