module Data.Vect.Utils

import Data.Fin
import Data.Vect

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

export
appendRightNeutral : {n : _} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
appendRightNeutral [] = Refl
appendRightNeutral {n = S n} (x :: xs) with (appendRightNeutral xs)
  _ | rec with (plusZeroRightNeutral n)
             | (plus n Z)
    _ | Refl | _ = cong (x ::) rec
