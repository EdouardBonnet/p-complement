The complexity class $\mathrm{P}$ consists of the languages of binary strings
decided by deterministic Turing machines in polynomial time. We formalize this
definition using Boolean characteristic functions, the identity encoding of
binary strings, and a one-bit encoding of the answer. Polynomial time is
measured by the transitions of mathlib's bundled multi-stack Turing machines.

We independently define polynomial-time decision by elementary single-tape
machines with finite alphabets and control states, and prove equality with
the stack-machine class. Both directions have formally proved polynomial
simulation bounds, including input preparation and output cleanup. Requiring
finite alphabets at all work stacks is also proved to preserve the class.

We prove that $\mathrm{P}$ is closed under complement. Exchanging the two output
symbols of a deciding machine reverses its answer while preserving its
execution and its polynomial time bound. The model equivalence gives complement
closure for the elementary single-tape definition as well.
