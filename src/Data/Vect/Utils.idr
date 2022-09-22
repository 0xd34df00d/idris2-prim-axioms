module Data.Vect.Utils

import Data.Vect

%default total

export
appendRightNeutral : {n : _} ->
                     (xs : Vect n a) ->
                     xs ++ [] ~=~ xs
appendRightNeutral [] = Refl
appendRightNeutral {n = S n} (x :: xs) with (appendRightNeutral xs)
  _ | rec with (plusZeroRightNeutral n)
             | (plus n Z)
    _ | Refl | _ = cong (x ::) rec
