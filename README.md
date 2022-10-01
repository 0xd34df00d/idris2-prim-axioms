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

### General structure

The primary module of interest is `Data.Bits.Verified`,
which both defines the `VerifiedBits` interface and the helper functions.
Another important module is `Data.Bits.Verified.Prim`,
which actually defines the instances of `VerifiedBits` for the primitive types
(and reexports `Data.Bits.Verified`).

### Naming conventions

The proof-producing helper functions generally have a `**` at the side about which they prove things.
For instance:

* `v1 .>>.** v2` produces a resulting value and a proof that the result is less than `2` to the power of `bitSize - v2`.
* `v1 .&.** v2` produces a resulting value and a proof that the result is less than or equal to `v2`.

The helpers that produce `Fin bitSize` have `|` at the side which is related to the bound,
and they generally also have an implicit `auto`-searchable proof argument for the said side to be appropriate.
For instance:

* `v1 .&.| v2` wraps the result of bit-`and` into `Fin bitSize`, requiring an (implicit) proof of `v2` being less than the `bitSize`.
* `v1 .>>.| v2` wraps the result of the right shift into `Fin bitSize`,
  requiring an (implicit) proof of `v2` being large enough for `2` to the power of `bitSize - v2` to be less than `bitSize`.

Generally, for static arguments (like in the motivating example) Idris is able to find these proofs itself.
