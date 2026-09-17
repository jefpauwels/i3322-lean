import I3322.MainTheorems

/-!
# Theorems 1 and 2

Paper references use arXiv:2608.29734v1,
https://arxiv.org/abs/2608.29734v1.

The definitions needed for both theorem statements are collected below.
The quantum strategies consist of complex pure states and three binary
projective measurements per party, in arbitrary positive finite local
dimensions. The purification and Naimark dilation in Section III A are not
formalized here.

Lean indices start at zero: `alice 0` is `A₁`, and `amplitude 0` is `λ₁`.
-/

namespace I3322.Statement

/-! ## Quantum strategies and their Bell values -/

/-- An outcome-`1` projector on `ℂⁿ`: a Hermitian matrix `P` with `P² = P`.
The outcome-`0` projector is `1 - P`. -/
structure OrthogonalProjection (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  hermitian : matrix.conjTranspose = matrix
  idempotent : matrix * matrix = matrix

/-- The pure states and binary projective measurements of Section III A,
with the probabilities of Section II A. The coefficient
`state i j` multiplies the basis vector `|i⟩ ⊗ |j⟩`.
The dimensions need not agree, and the state need not be normalized. -/
structure QuantumStrategy where
  dimA : ℕ
  dimB : ℕ
  dimA_pos : 0 < dimA
  dimB_pos : 0 < dimB
  state : Matrix (Fin dimA) (Fin dimB) ℂ
  stateNormSq_pos :
    0 < ∑ i : Fin dimA, ∑ j : Fin dimB, Complex.normSq (state i j)
  alice : Fin 3 → OrthogonalProjection dimA
  bob : Fin 3 → OrthogonalProjection dimB

namespace QuantumStrategy

/-- `⟨ψ|ψ⟩ = ∑ᵢⱼ |ψᵢⱼ|²`, strictly positive by the strategy definition. -/
noncomputable def stateNormSq (S : QuantumStrategy) : ℝ :=
  ∑ i : Fin S.dimA, ∑ j : Fin S.dimB, Complex.normSq (S.state i j)

/-- The Born-rule expression `⟨ψ| A ⊗ B |ψ⟩`.
Here `star` is complex conjugation. -/
noncomputable def bornNumerator (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) : ℂ :=
  ∑ i : Fin S.dimA, ∑ j : Fin S.dimB,
    ∑ k : Fin S.dimA, ∑ l : Fin S.dimB,
      star (S.state i j) * A i k * B j l * S.state k l

/-- The expectation value `⟨ψ| A ⊗ B |ψ⟩ / ⟨ψ|ψ⟩`.
For the Hermitian operators below, the numerator is real; `.re` takes its real part. -/
noncomputable def expectation (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) : ℝ :=
  (S.bornNumerator A B).re / S.stateNormSq

/-- `P(11|xy)`. -/
noncomputable def joint (S : QuantumStrategy) (x y : Fin 3) : ℝ :=
  S.expectation (S.alice x).matrix (S.bob y).matrix

/-- `P_A(1|x)`; the matrix `1` is Bob's identity operator. -/
noncomputable def aliceMarginal (S : QuantumStrategy) (x : Fin 3) : ℝ :=
  S.expectation (S.alice x).matrix 1

/-- `P_B(1|y)`; the matrix `1` is Alice's identity operator. -/
noncomputable def bobMarginal (S : QuantumStrategy) (y : Fin 3) : ℝ :=
  S.expectation 1 (S.bob y).matrix

/-- Equation (1), the paper's `I₃₃₂₂`:
`-⟨A₂⟩ - ⟨B₁⟩ - 2⟨B₂⟩ + ⟨A₁B₁⟩ + ⟨A₁B₂⟩ + ⟨A₂B₁⟩ + ⟨A₂B₂⟩
 - ⟨A₁B₃⟩ + ⟨A₂B₃⟩ - ⟨A₃B₁⟩ + ⟨A₃B₂⟩`.
Lean counts from zero: `alice 1` is `A₂`, `bob 0` is `B₁`, and `joint 0 2` is `⟨A₁B₃⟩`. -/
noncomputable def value (S : QuantumStrategy) : ℝ :=
  -S.aliceMarginal 1 - S.bobMarginal 0 - 2 * S.bobMarginal 1
    + S.joint 0 0 + S.joint 0 1 + S.joint 1 0 + S.joint 1 1
    - S.joint 0 2 + S.joint 1 2 - S.joint 2 0 + S.joint 2 1

end QuantumStrategy

/-- Equation (2), for the pure states and projective measurements above.
`Set.range QuantumStrategy.value` is the set of all their Bell values, and `sSup`
is its least upper bound. Mathlib gives `sSup` the value `0` on a set of reals that
is empty or unbounded above; `quantumValues_nonempty` and `quantumValues_bddAbove`
below exclude both cases. -/
noncomputable def quantumSupremum : ℝ :=
  sSup (Set.range QuantumStrategy.value)

/-! ## The Pál–Vértesi family -/

/-- Equation (4): `s(c) = √(1 - c²)`. -/
noncomputable def s (c : ℝ) : ℝ :=
  Real.sqrt (1 - c ^ 2)

/-- Equation (4): `d(a,b) = ab + (a-b)/2 - 1`. -/
noncomputable def d (a b : ℝ) : ℝ :=
  a * b + (a - b) / 2 - 1

/-- The domain in Equation (7): a finite chain of length `n ≥ 1`
with labels `c₀,…,cₙ` in `[-1,1]`,
endpoints `c₀ = 1`, `cₙ = -1`, and nonnegative Schmidt coefficients that are not all zero.
`amplitude i` is the paper's `λᵢ₊₁`. Only `label 0,…,label n` and
`amplitude 0,…,amplitude (n-1)` are used; values elsewhere are irrelevant. -/
structure PVChain where
  n : ℕ
  n_pos : 0 < n
  label : ℕ → ℝ
  amplitude : ℕ → ℝ
  label_mem : ∀ i, i ≤ n → label i ∈ Set.Icc (-1 : ℝ) 1
  leftEndpoint : label 0 = 1
  rightEndpoint : label n = -1
  amplitude_nonneg : ∀ i, i < n → 0 ≤ amplitude i
  normSq_pos : 0 < ∑ i ∈ Finset.range n, amplitude i ^ 2

namespace PVChain

/-- The sum of squared Schmidt coefficients. `Finset.range n` is `{0,…,n-1}`. -/
noncomputable def normSq (p : PVChain) : ℝ :=
  ∑ i ∈ Finset.range p.n, p.amplitude i ^ 2

/-- The numerator of Equation (5):
`∑ᵢ₌₁ⁿ d(cᵢ₋₁,cᵢ) λᵢ² + ∑ᵢ₌₁ⁿ⁻¹ s(cᵢ) λᵢ λᵢ₊₁`.
For `n = 1` the second sum is empty. -/
noncomputable def numerator (p : PVChain) : ℝ :=
  (∑ i ∈ Finset.range p.n,
      d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2) +
    ∑ i ∈ Finset.range (p.n - 1),
      s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)

/-- Equation (5): the PV value `𝒫ₙ(c,λ)`; its denominator is positive. -/
noncomputable def value (p : PVChain) : ℝ :=
  p.numerator / p.normSq

end PVChain

/-- Equation (7): `β_PV`, the least upper bound of the values of all the finite
chains just defined. `pvValues_nonempty` and `pvValues_bddAbove` below show that
`sSup` is the genuine supremum here. -/
noncomputable def betaPV : ℝ :=
  sSup (Set.range PVChain.value)

/-! ## Equality of the sets of values

The definitions above give the same sets of Bell values and PV values as
`I3322.QuantumStrategy` and `I3322.PVChain`. The equalities below identify
the two suprema.
-/

private def quantumToOriginal (S : QuantumStrategy) : I3322.QuantumStrategy where
  dimA := S.dimA
  dimB := S.dimB
  dimA_pos := S.dimA_pos
  dimB_pos := S.dimB_pos
  state := S.state
  stateNormSq_pos := S.stateNormSq_pos
  alice := fun x => ⟨(S.alice x).matrix, (S.alice x).hermitian,
    (S.alice x).idempotent⟩
  bob := fun y => ⟨(S.bob y).matrix, (S.bob y).hermitian,
    (S.bob y).idempotent⟩

private def quantumFromOriginal (S : I3322.QuantumStrategy) : QuantumStrategy where
  dimA := S.dimA
  dimB := S.dimB
  dimA_pos := S.dimA_pos
  dimB_pos := S.dimB_pos
  state := S.state
  stateNormSq_pos := S.stateNormSq_pos
  alice := fun x => ⟨(S.alice x).matrix, (S.alice x).hermitian,
    (S.alice x).idempotent⟩
  bob := fun y => ⟨(S.bob y).matrix, (S.bob y).hermitian,
    (S.bob y).idempotent⟩

private def pvToOriginal (p : PVChain) : I3322.PVChain where
  n := p.n
  n_pos := p.n_pos
  label := p.label
  amplitude := p.amplitude
  label_mem := p.label_mem
  leftEndpoint := p.leftEndpoint
  rightEndpoint := p.rightEndpoint
  amplitude_nonneg := p.amplitude_nonneg
  normSq_pos := p.normSq_pos

private def pvFromOriginal (p : I3322.PVChain) : PVChain where
  n := p.n
  n_pos := p.n_pos
  label := p.label
  amplitude := p.amplitude
  label_mem := p.label_mem
  leftEndpoint := p.leftEndpoint
  rightEndpoint := p.rightEndpoint
  amplitude_nonneg := p.amplitude_nonneg
  normSq_pos := p.normSq_pos

private theorem quantumValues_eq :
    Set.range QuantumStrategy.value = Set.range I3322.QuantumStrategy.value := by
  ext v
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨quantumToOriginal S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨quantumFromOriginal S, rfl⟩

private theorem pvValues_eq :
    Set.range PVChain.value = Set.range I3322.PVChain.value := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨pvToOriginal p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨pvFromOriginal p, rfl⟩

private theorem quantumSupremum_eq_original :
    quantumSupremum = I3322.quantumSupremum := by
  unfold quantumSupremum I3322.quantumSupremum
  rw [quantumValues_eq]

private theorem betaPV_eq_original : betaPV = I3322.betaPV := by
  unfold betaPV I3322.betaPV
  rw [pvValues_eq]

/-! ## The two main theorems

Both sets of values are nonempty and bounded above, so both `sSup` are least
upper bounds in the usual sense.
-/

/-- At least one finite quantum strategy exists. -/
theorem quantumValues_nonempty : (Set.range QuantumStrategy.value).Nonempty := by
  rw [quantumValues_eq]
  exact I3322.quantumValues_nonempty

/-- The set of finite quantum Bell values has an upper bound. -/
theorem quantumValues_bddAbove : BddAbove (Set.range QuantumStrategy.value) := by
  rw [quantumValues_eq]
  exact I3322.quantumValues_bddAbove

/-- At least one finite PV chain exists. -/
theorem pvValues_nonempty : (Set.range PVChain.value).Nonempty := by
  rw [pvValues_eq]
  exact I3322.pvValues_nonempty

/-- The set of finite PV-chain values has an upper bound. -/
theorem pvValues_bddAbove : BddAbove (Set.range PVChain.value) := by
  rw [pvValues_eq]
  exact I3322.pvValues_bddAbove

/-- **Theorem 1, Equation (8).** The quantum supremum equals `β_PV`,
for the pure states and binary projective measurements defined above. -/
theorem variational : quantumSupremum = betaPV := by
  rw [quantumSupremum_eq_original, betaPV_eq_original]
  exact I3322.quantumSupremum_eq_betaPV

/-- **Theorem 2.** No finite-dimensional strategy defined above
attains the quantum supremum. -/
theorem finiteDimensional_nonattainment :
    ∀ S : QuantumStrategy, S.value ≠ quantumSupremum := by
  intro S hS
  apply I3322.finiteDimensional_nonattainment (quantumToOriginal S)
  calc
    (quantumToOriginal S).value = S.value := rfl
    _ = quantumSupremum := hS
    _ = I3322.quantumSupremum := quantumSupremum_eq_original

/-! ## Two consistency checks

These theorems relate the definitions above to facts that can be checked
independently of the main proof. -/

/-- Section II B: the value of every PV chain is the Bell value of an explicit
finite-dimensional strategy. The Bell functional and the Born rule defined
above therefore reproduce Equation (5) on the Pál–Vértesi family. -/
theorem pvValue_attained (p : PVChain) :
    ∃ S : QuantumStrategy, S.value = p.value := by
  obtain ⟨S, hS⟩ := I3322.PVRealization.exists_quantumStrategy (pvToOriginal p)
  exact ⟨quantumFromOriginal S, hS⟩

/-- Equation (30), proved in Appendix C:
`1/4 < β_PV < 1/3`. -/
theorem betaPV_bounds : (1 / 4 : ℝ) < betaPV ∧ betaPV < 1 / 3 := by
  rw [betaPV_eq_original]
  exact ⟨I3322.quarter_lt_betaPV, I3322.betaPV_lt_third⟩

end I3322.Statement
