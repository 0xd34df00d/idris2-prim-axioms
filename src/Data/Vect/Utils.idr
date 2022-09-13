module Data.Vect.Utils

import Data.Fin
import Data.Vect

%default total

public export
data SplitDirection = FromLeft | FromRight

public export
data SplitResult : {n : Nat} -> SplitDirection -> (pos : Fin n) -> (xs : Vect n a) -> Type where
  TheSplit : {n1, n2 : _}
          -> {dir : SplitDirection}
          -> {pos : Fin (n1 + n2)}
          -> (before : Vect n1 a)
          -> (after : Vect n2 a)
          -> (eq : case dir of FromLeft  => n1 = finToNat pos
                               FromRight => n2 = finToNat pos)
          -> SplitResult dir pos (before ++ after)

export
splitAtFin : {n : _} -> (pos : Fin n) -> (xs : Vect n a) -> SplitResult pos xs
splitAtFin FZ xs = TheSplit [] xs Refl
splitAtFin (FS pos) (x :: xs) with (splitAtFin pos xs)
  splitAtFin (FS pos) (x :: before ++ after) | TheSplit before after eq = TheSplit (x :: before) after (cong S eq)

export
appendRightNeutral : {n : _} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
appendRightNeutral [] = Refl
appendRightNeutral {n = S n} (x :: xs) with (appendRightNeutral xs)
  _ | rec with (plusZeroRightNeutral n)
             | (plus n Z)
    _ | Refl | _ = cong (x ::) rec
