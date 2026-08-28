# I3322 in Lean 4

[![Lean CI](https://github.com/jefpauwels/i3322-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/jefpauwels/i3322-lean/actions/workflows/lean.yml)

This repository contains Lean 4 proofs of the following two theorems:

```lean
I3322.quantumSupremum_eq_betaPV : quantumSupremum = betaPV

I3322.finiteDimensional_nonattainment :
  ∀ S : QuantumStrategy, S.value ≠ quantumSupremum
```

## Formal scope

[`QuantumStrategy`](I3322/QuantumStrategy.lean) consists of two positive
finite local dimensions, a nonzero (not necessarily normalized) complex
bipartite pure-state vector, and three binary projective measurements for each
party. Born values are divided by the vector's squared norm. With one-based
measurement labels, the encoded Bell functional is

```text
-<A2> - <B1> - 2<B2>
+ <A1 B1> + <A1 B2> + <A2 B1> + <A2 B2>
- <A1 B3> + <A2 B3> - <A3 B1> + <A3 B2>.
```

Here `<Ax>` and `<By>` are outcome-`1` marginal probabilities, and
`<Ax By>` is the joint outcome-`(1,1)` probability.

[`PVChain`](I3322/PV.lean) encodes finite Pál–Vértesi chains with labels in
`[-1,1]`, endpoints `1` and `-1`, nonnegative amplitudes, and positive squared
norm. The two suprema are

```lean
I3322.quantumSupremum = sSup (Set.range QuantumStrategy.value)
I3322.betaPV = sSup (Set.range PVChain.value)
```

The theorem quantifiers are exactly over this pure-state/projective-measurement
model. The usual finite-dimensional reduction from mixed states and binary
POVMs by purification and Naimark dilation is not formalized here. Neither are
general infinite-dimensional or commuting-operator strategies.

The development proves the additional coarse enclosure

```text
1/4 < betaPV ≤ (sqrt 5 - 1)/4 < 1/3.
```

It does not formalize an exact numerical or closed-form value of `betaPV`,
uniqueness, infinite-dimensional attainment, or a dimension-convergence rate.

## Proof map

The [dependency graph](docs/lean_proof_graph.pdf) summarizes the proof; its
[LaTeX source](docs/lean_proof_graph.tex) is included. The principal modules
are:

| Role | Source |
| --- | --- |
| Concrete quantum and Pál–Vértesi definitions | [`QuantumStrategy.lean`](I3322/QuantumStrategy.lean), [`PV.lean`](I3322/PV.lean) |
| Realization of every finite PV chain as a quantum strategy | [`PVRealization.lean`](I3322/PVRealization.lean) |
| Operator-to-coupling-table upper bound | [`OperatorReduction.lean`](I3322/OperatorReduction.lean) |
| Coupling-table bound by the PV supremum | [`TableToPV.lean`](I3322/TableToPV.lean) |
| Equality extraction and strictness | [`EqualityExtraction.lean`](I3322/EqualityExtraction.lean), [`FiniteSpine.lean`](I3322/FiniteSpine.lean) |
| Final theorem assembly | [`MainTheorems.lean`](I3322/MainTheorems.lean) |

At declaration level, explicit PV realization proves
`betaPV_le_quantumSupremum`; `QuantumStrategy.tableBound` and
`CouplingTable.Ensemble.score_le_betaPV` prove the reverse inequality; and
`CouplingTable.score_ne_betaPV` gives nonattainment within `QuantumStrategy`.

## Build

The project is pinned to Lean, mathlib, and Physlib `v4.32.0`; the exact
dependency commits are recorded in [`lake-manifest.json`](lake-manifest.json).
All `I3322`-specific definitions and bridge theorems are local to this
repository. Mathlib supplies the foundational real, complex, matrix,
analytic, and order-theoretic results; Physlib supplies imported Schatten-
and trace-norm infrastructure.

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

Here `propext`, `Classical.choice`, and `Quot.sound` are Lean's standard
principles for propositional extensionality, classical choice, and quotients;
none is a physical or mathematical assumption specific to `I3322`. No
operator reduction, PV inequality, stationarity equation, or nonattainment
step is postulated.

## Citation and license

Citation metadata are provided in [`CITATION.cff`](CITATION.cff). The source is
available under the [`MIT License`](LICENSE).
