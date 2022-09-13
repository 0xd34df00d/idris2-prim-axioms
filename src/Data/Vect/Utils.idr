module Data.Vect.Utils

import Data.Fin
import Data.Vect

%default total

export
appendRightNeutral : {n : _} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
appendRightNeutral [] = Refl
appendRightNeutral {n = S n} (x :: xs) with (appendRightNeutral xs)
  _ | rec with (plusZeroRightNeutral n)
             | (plus n Z)
    _ | Refl | _ = cong (x ::) rec


lstInjectiveHead : {xs, ys : List a}
                -> x :: xs = y :: ys
                -> x = y
lstInjectiveHead Refl = Refl

lstInjectiveTail : {xs, ys : List a}
                -> x :: xs = y :: ys
                -> xs = ys
lstInjectiveTail Refl = Refl

vecToList : Vect n a -> List a
vecToList [] = []
vecToList (x :: xs) = x :: vecToList xs

vecToListHomo : (xs, ys : _)
             -> vecToList xs = vecToList ys
             -> xs = ys
vecToListHomo [] [] _ = Refl
vecToListHomo (x :: xs) (y :: ys) prf = case lstInjectiveHead prf of
                                             Refl => cong (x ::) $ vecToListHomo xs ys (lstInjectiveTail prf)

export
reverseParts : {m, n : _}
            -> (xs : Vect m a)
            -> (ys : Vect n a)
            -> xs ++ ys ~=~ reverse (reverse ys ++ reverse xs)
reverseParts {n = n} [] ys = let r = appendRightNeutral (reverse ys) in
                                 rewrite plusZeroRightNeutral n in
                                         -- rewrite appendRightNeutral (reverse ys) in
                                                 ?reverseParts_rhs_0
reverseParts (x :: xs) ys = ?reverseParts_rhs_1


public export
data SplitDirection = FromLeft | FromRight

public export %inline
splitDirDestr : (l, r : a) -> SplitDirection -> a
splitDirDestr l r dir = case dir of
                             FromLeft => l
                             FromRight => r

public export
data SplitResult : {n : Nat} -> SplitDirection -> (pos : Fin n) -> (xs : Vect n a) -> Type where
  TheSplit : {n1, n2 : _}
          -> {dir : SplitDirection}
          -> {pos : Fin (n1 + n2)}
          -> (before : Vect n1 a)
          -> (after : Vect n2 a)
          -> (eq : splitDirDestr n1 n2 dir = finToNat pos)
          -> SplitResult dir pos (before ++ after)

export
splitLAtFin : {n : _} -> (pos : Fin n) -> (xs : Vect n a) -> SplitResult FromLeft pos xs
splitLAtFin FZ xs = TheSplit [] xs Refl
splitLAtFin (FS pos) (x :: xs) with (splitLAtFin pos xs)
  splitLAtFin (FS pos) (x :: before ++ after) | TheSplit before after eq = TheSplit (x :: before) after (cong S eq)
