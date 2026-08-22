# I3322 in Lean 4

Lean 4 formalization of the following results:

```lean
I3322.quantumSupremum_eq_betaPV : quantumSupremum = betaPV

I3322.finiteDimensional_nonattainment :
  ∀ S : QuantumStrategy, S.value ≠ quantumSupremum
```

`QuantumStrategy` consists of a finite-dimensional complex bipartite pure
state and three binary projective measurements for each party. Its value is
defined by finite Born-rule sums. The two suprema are

```lean
I3322.quantumSupremum = sSup (Set.range QuantumStrategy.value)
I3322.betaPV = sSup (Set.range PVChain.value)
```

The reduction from mixed states and binary POVMs to this pure-projective model
is not formalized here.

## Build

The project is pinned to Lean, mathlib, and Physlib `v4.32.0`.

```sh
lake exe cache get
lake build I3322
```

## Axiom audit

```sh
lake env lean Audit.lean
```

For the two main theorems, Lean reports:

```text
[propext, Classical.choice, Quot.sound]
```

The source contains no `sorry`, `admit`, or project-specific axiom.
