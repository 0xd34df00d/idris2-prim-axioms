module Data.Vect.Utils

import Data.Fin
import Data.Vect

%default total

public export
data SplitResult : (n : Nat) -> (pos : Fin n) -> (a : Type) -> Type where
  TheSplit : {n1, n2 : _}
          -> {pos : Fin (n1 + n2)}
          -> (before : Vect n1 a)
          -> (after : Vect n2 a)
          -> (eq : n1 = finToNat pos)
          -> SplitResult (n1 + n2) pos a

export
splitAtFin : {n : _} -> (pos : Fin n) -> Vect n a -> SplitResult n pos a
splitAtFin FZ xs = TheSplit [] xs Refl
splitAtFin (FS pos) (x :: xs) with (splitAtFin pos xs)
  _ | TheSplit before after eq = TheSplit (x :: before) after (cong S eq)
