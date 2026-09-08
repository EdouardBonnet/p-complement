# Polynomial Time and Closure under Complement

Lax submission `lax-554803`, using Lean `v4.30.0` and mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

A language is a set of finite binary strings. It belongs to P when a Boolean
characteristic function is computed by a deterministic Turing machine within
a polynomial bound in the input length. The definition uses mathlib's
`Turing.TM2ComputableInPolyTime`, with the identity input encoding and a
singleton Boolean output encoding.

The complement construction composes the output-alphabet equivalence with
Boolean negation. It preserves the underlying machine, the input encoding,
and the time polynomial. The existing execution certificate therefore proves
the time bound for the complemented answer.

- [Definition of P](concepts/Lax554803/PolynomialTime.lean)
- [Complement closure statement](concepts/Lax554803/ComplementClosure.lean)
- [Machine construction and proof](proofs/Lax554803Proofs/ComplementClosure.lean)

Following Lax's format, the concept package declares the closure statement as
an axiom. The proof package proves that statement without assuming it.

From this directory, run the complete archive checks, including kernel replay:

```sh
lax build . --replay
```

For Lean compilation during editing:

```sh
cd proofs
lake build
```
