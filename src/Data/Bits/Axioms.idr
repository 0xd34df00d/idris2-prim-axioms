module Data.Bits.Axioms

import Data.Vect
import Decidable.Equality

%default total

public export
data Bit = I | O

public export
DecEq Bit where
  decEq I I = Yes Refl
  decEq I O = No \case Refl impossible
  decEq O I = No \case Refl impossible
  decEq O O = Yes Refl

public export
zipRAccum : (f : accTy -> a -> b -> (c, accTy)) -> (acc : accTy) -> (xs : Vect w a) -> (ys : Vect w b) -> (Vect w c, accTy)
zipRAccum f acc [] [] = ([], acc)
zipRAccum f acc (x :: xs) (y :: ys)
  = let (zs, acc') = zipRAccum f acc xs ys
        (z, acc'') = f acc' x y
     in (z :: zs, acc'')

add : Bit -> Bit -> (Bit, Bit)
add O O = (O, O)
add I O = (O, I)
add O I = (O, I)
add I I = (I, O)

addWithCarry : Bit -> Bit -> Bit -> (Bit, Bit)
addWithCarry carry b1 b2 = ?w

namespace Unsigned
  public export
  data Unsigned : (w : Nat) -> Type where
    MkU : (bits : Vect w Bit) -> Unsigned w

  -- Example:
  public export
  Unsigned64 : Type
  Unsigned64 = Unsigned 64

  powNat : Num a => a -> Nat -> a
  powNat _ Z = 1
  powNat x (S y) = x * powNat x y

  zero : {w : _} -> Unsigned w
  zero = MkU $ replicate _ O

  public export
  DecEq (Unsigned w) where
    decEq (MkU b1) (MkU b2) = case decEq b1 b2 of
                                   Yes Refl => Yes Refl
                                   No contra => No \case Refl => contra Refl

  public export
  add : (n1, n2 : Unsigned w) -> Unsigned w
  add (MkU b1) (MkU b2) = MkU $ fst $ zipRAccum addWithCarry O b1 b2

  public export
  mul : (n1, n2 : Unsigned w) -> Unsigned w

  public export
  Num (Unsigned w) where
    fromInteger n = ?fi
    (+) = add
    (*) = mul
