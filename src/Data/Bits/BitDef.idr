module Data.Bits.BitDef

import Decidable.Equality

%default total

public export
data Bit = O | I

public export
DecEq Bit where
  decEq I I = Yes Refl
  decEq I O = No $ \case Refl impossible
  decEq O I = No $ \case Refl impossible
  decEq O O = Yes Refl

public export
and : Bit -> Bit -> Bit
and I b = b
and _ _ = O

public export
or : Bit -> Bit -> Bit
or O b = b
or _ _ = I

public export
xor : Bit -> Bit -> Bit
xor I O = I
xor O I = I
xor _ _ = O

public export
not : Bit -> Bit
not O = I
not I = O

public export
toBool : Bit -> Bool
toBool O = False
toBool I = True

export
andRightId : (b : Bit)
          -> b `and` I = b
andRightId O = Refl
andRightId I = Refl

export
andLeftId : (b : Bit)
         -> I `and` b = b
andLeftId _ = Refl

export
andRightZero : (b : Bit)
            -> b `and` O = O
andRightZero O = Refl
andRightZero I = Refl

export
andLeftZero : (b : Bit)
           -> O `and` b = O
andLeftZero _ = Refl

export
andCommutes : (b1, b2 : Bit)
           -> b1 `and` b2 = b2 `and` b1
andCommutes O b2 = case b2 of { O => Refl ; I => Refl }
andCommutes I b2 = case b2 of { O => Refl ; I => Refl }
