## Provable/axiomatic properties of bit operations

This package contains some primitives for (verified) bit operations.
Concretely, it provides some lemmas about how bit ops on primitive types (like `Bits64`) behave,
like commutativity of `.&.`, or the bounds on `shiftR`.

It also provides some helpers to simplify writing complex chains of bit operations.
For instance, suppose you want to use the result of right-shifting a `Bits64` number
by `59` as a value of another shift.
You might attempt to write
```idris
let shift = val `shiftR` 59
 in val `shiftR` shift
```
but this won't type check, since the type of `shift` is `Bits64`,
while the second argument of `shiftR` in this case shall be `Fin 64`.

Here, a function like `.>>.|` from this library could be used instead,
and this type checks:
```idris
let shift = val .>>.| 59
 in val `shiftR` shift
```
