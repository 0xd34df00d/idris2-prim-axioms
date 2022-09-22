module Data.Vect.Reverse

import Data.Fin
import Data.List
import Data.Vect

%default total

-- TODO remove this if/when `go` is moved outside of the `where` clause in base libs
public export
reverse'Onto : Vect n a ->
               Vect m a ->
               Vect (n + m) a
reverse'Onto {n}           acc []        = rewrite plusZeroRightNeutral n in acc
reverse'Onto {n} {m = S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m in reverse'Onto (x :: acc) xs

public export
reverse' : Vect len a ->
           Vect len a
reverse' = reverse'Onto []


lstInjectiveHead : {xs, ys : List a} ->
                   x :: xs = y :: ys ->
                   x = y
lstInjectiveHead Refl = Refl

lstInjectiveTail : {xs, ys : List a} ->
                   x :: xs = y :: ys ->
                   xs = ys
lstInjectiveTail Refl = Refl

vecToList : Vect n a -> List a
vecToList [] = []
vecToList (x :: xs) = x :: vecToList xs

vecToListHomo : (xs, ys : _) ->
                vecToList xs = vecToList ys ->
                xs = ys
vecToListHomo [] [] _ = Refl
vecToListHomo (x :: xs) (y :: ys) prf = case lstInjectiveHead prf of
                                             Refl => cong (x ::) $ vecToListHomo xs ys (lstInjectiveTail prf)

vecToListSizeHomo : (xs : Vect m a) ->
                    (ys : Vect n a) ->
                    vecToList xs = vecToList ys ->
                    m = n
vecToListSizeHomo [] [] prf = Refl
vecToListSizeHomo [] (_ :: _) Refl impossible
vecToListSizeHomo (_ :: _) [] Refl impossible
vecToListSizeHomo (_ :: xs) (_ :: ys) prf = cong S $ vecToListSizeHomo xs ys (lstInjectiveTail prf)

vecToListHomoHetero : (xs : Vect m a) ->
                      (ys : Vect n a) ->
                      vecToList xs = vecToList ys ->
                      xs = ys
vecToListHomoHetero xs ys prf = case vecToListSizeHomo xs ys prf of Refl => vecToListHomo xs ys prf

vecToListConcat : (xs : Vect n a) ->
                  (ys : Vect m a) ->
                  vecToList (xs ++ ys) = vecToList xs ++ vecToList ys
vecToListConcat [] _ = Refl
vecToListConcat (x :: xs) ys = cong (x ::) $ vecToListConcat xs ys

vecToListReverseOnto : (acc : Vect n a) ->
                       (xs : Vect m a) ->
                       vecToList (reverse'Onto acc xs) = reverseOnto (vecToList acc) (vecToList xs)
vecToListReverseOnto acc [] = Refl
vecToListReverseOnto acc (x :: xs) = vecToListReverseOnto (x :: acc) xs

vecToListReverse : (xs : Vect n a) ->
                   vecToList (reverse' xs) = reverse (vecToList xs)
vecToListReverse = vecToListReverseOnto []

export
reverseAppend : (xs : Vect m a) ->
                (ys : Vect n a) ->
                reverse' ys ++ reverse' xs ~=~ reverse' (xs ++ ys)
reverseAppend xs ys = vecToListHomoHetero _ _ $
                        rewrite vecToListReverse (xs ++ ys) in
                        rewrite vecToListConcat (reverse' ys) (reverse' xs) in
                        rewrite vecToListConcat xs ys in
                        rewrite vecToListReverse xs in
                        rewrite vecToListReverse ys in
                        rewrite revAppend (vecToList xs) (vecToList ys) in
                                Refl

export
reverseConcat : (xs : Vect m a) ->
                (ys : Vect n a) ->
                xs ++ ys ~=~ reverse' (reverse' ys ++ reverse' xs)
reverseConcat xs ys = vecToListHomoHetero _ _ $
                        rewrite vecToListReverse (reverse' ys ++ reverse' xs) in
                        rewrite vecToListConcat (reverse' ys) (reverse' xs) in
                        rewrite vecToListReverse ys in
                        rewrite vecToListReverse xs in
                        rewrite revAppend (vecToList xs) (vecToList ys) in
                        rewrite sym $ vecToListConcat xs ys in
                        rewrite reverseInvolutive (vecToList (xs ++ ys)) in
                                Refl

export
reverseInvolutive : (xs : Vect n a) ->
                    xs = reverse' (reverse' xs)
reverseInvolutive xs = vecToListHomo _ _ $
                        rewrite vecToListReverse (reverse' xs) in
                        rewrite vecToListReverse xs in
                        rewrite reverseInvolutive (vecToList xs) in
                                Refl
