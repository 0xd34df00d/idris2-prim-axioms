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
and I I = I
and _ _ = O

public export
or : Bit -> Bit -> Bit
or O O = O
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
