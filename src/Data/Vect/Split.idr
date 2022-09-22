module Data.Vect.Split

import Data.Fin
import Data.Vect

import Data.Vect.Reverse

%default total

public export
data SplitDirection = FromLeft | FromRight

public export %inline
splitDirDestr : (l, r : a) -> SplitDirection -> a
splitDirDestr l r dir = case dir of
                             FromLeft => l
                             FromRight => r

public export
data SplitResult : {n : Nat} -> SplitDirection -> (pos : Fin n) -> (xs : Vect n a) -> Type where
  TheSplit : {n1, n2 : _} ->
             {dir : SplitDirection} ->
             {pos : Fin (n1 + n2)} ->
             (before : Vect n1 a) ->
             (after : Vect n2 a) ->
             (eq : splitDirDestr n1 n2 dir = finToNat pos) ->
             SplitResult dir pos (before ++ after)

export
splitLAtFin : {n : _} ->
              (pos : Fin n) ->
              (xs : Vect n a) ->
              SplitResult FromLeft pos xs
splitLAtFin FZ xs = TheSplit [] xs Refl
splitLAtFin (FS pos) (x :: xs) with (splitLAtFin pos xs)
  splitLAtFin (FS pos) (x :: before ++ after) | TheSplit before after eq = TheSplit (x :: before) after (cong S eq)

splitRAtFinHelper : {n1, n2 : Nat} ->
                    (before : Vect n1 a) ->
                    (after : Vect n2 a) ->
                    (pos : Fin (n1 + n2)) ->
                    SplitResult FromRight (rewrite plusCommutative n2 n1 in pos) (reverse' after ++ reverse' before) ->
                    SplitResult FromRight pos (reverse' (before ++ after))
splitRAtFinHelper before after pos res with (reverseAppend before after)
                                          | (reverse' after ++ reverse' before)
  _ | eq | _ with (plusCommutative n1 n2)
                | (n1 + n2)
    _ | Refl | _ = case eq of Refl => res

export
splitRAtFin : {n : _} ->
              (pos : Fin n) ->
              (xs : Vect n a) ->
              SplitResult FromRight pos xs
splitRAtFin pos xs with (reverse' xs) proof rxsEq
  _ | rxs with (splitLAtFin pos rxs)
    splitRAtFin pos xs | rbefore ++ rafter | TheSplit {n1 = n1, n2 = n2} rbefore rafter eq
        = let rec = TheSplit {dir = FromRight} {pos = rewrite plusCommutative n2 n1 in pos} (reverse' rafter) (reverse' rbefore) eq
           in rewrite reverseInvolutive xs `trans` cong reverse' rxsEq in
                      splitRAtFinHelper rbefore rafter pos rec
