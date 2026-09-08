# Polynomial Time and Closure under Complement

Lax submission `lax-554803`, using Lean `v4.30.0` and mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

A language is a set of finite binary strings. It belongs to P when a Boolean
characteristic function is computed by a deterministic Turing machine within
a polynomial bound in the input length. The definition uses mathlib's
`Turing.TM2ComputableInPolyTime`, with the identity input encoding and a
singleton Boolean output encoding.

The submission also defines elementary single-tape P independently and proves
that it equals the original P. Its machines have finite alphabets and control
states, read binary input in its original order, and execute one move or write
per transition. The proof includes both compilers and their polynomial bounds,
including input preparation and output cleanup. A further equality shows that
requiring finite alphabets at every work stack does not change P.

The complement construction composes the output-alphabet equivalence with
Boolean negation. It preserves the underlying machine, the input encoding,
and the time polynomial. The existing execution certificate therefore proves
the time bound for the complemented answer.

- [Definition of P](concepts/Lax554803/PolynomialTime.lean)
- [Complement closure statement](concepts/Lax554803/ComplementClosure.lean)
- [Machine construction and proof](proofs/Lax554803Proofs/ComplementClosure.lean)
- [Independent machine models](concepts/Lax554803/MachineModels.lean)
- [Finite stack alphabets suffice](concepts/Lax554803/FiniteStackEquivalence.lean)
- [Single-tape characterization](concepts/Lax554803/ModelEquivalence.lean)
- [Single-tape complement closure](concepts/Lax554803/SingleTapeComplement.lean)
- [Model equivalence proofs and single-tape complement closure](proofs/Lax554803Proofs/ModelEquivalence.lean)

Following Lax's format, the concept package declares statements as axioms.
The proof package proves all four statements. The proof network records
finite-alphabet reduction before model equivalence, then model equivalence
and complement closure before single-tape complement closure. All statement
dependencies are discharged by proofs in this submission.

The [formalization audit](AUDIT.md) explains the machine semantics, finiteness
conditions, and proved time bounds. Its independent Lean checks
are in [audit/Checks.lean](audit/Checks.lean).

From this directory, run the complete archive checks, including kernel replay:

```sh
lax build . --replay
```

For Lean compilation during editing:

```sh
cd proofs
lake build
```
