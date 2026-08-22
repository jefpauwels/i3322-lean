import I3322.PV

/-!
# Finite coupling tables

This file directly encodes the finite tables and their score from
equations (20)--(21) of the manuscript.
-/

namespace I3322

/-- A nonnegative, unit-mass table on a finite set of labels in `[-1,1]`. -/
structure CouplingTable where
  Label : Type
  [fintypeLabel : Fintype Label]
  label : Label → ℝ
  label_injective : Function.Injective label
  label_mem : ∀ c, label c ∈ Set.Icc (-1 : ℝ) 1
  weight : Label → Label → ℝ
  weight_nonneg : ∀ a b, 0 ≤ weight a b
  totalWeight : ∑ a, ∑ b, weight a b = 1

namespace CouplingTable

attribute [instance] CouplingTable.fintypeLabel

/-- The row marginal `R_a`. -/
noncomputable def row (θ : CouplingTable) (a : θ.Label) : ℝ :=
  ∑ b, θ.weight a b

/-- The column marginal `C_b`. -/
noncomputable def column (θ : CouplingTable) (b : θ.Label) : ℝ :=
  ∑ a, θ.weight a b

/-- The table score `Phi(theta)` from equation (21). -/
noncomputable def score (θ : CouplingTable) : ℝ :=
  (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
    ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c)

theorem row_nonneg (θ : CouplingTable) (a : θ.Label) : 0 ≤ θ.row a := by
  exact Finset.sum_nonneg fun b _ => θ.weight_nonneg a b

theorem column_nonneg (θ : CouplingTable) (b : θ.Label) : 0 ≤ θ.column b := by
  exact Finset.sum_nonneg fun a _ => θ.weight_nonneg a b

end CouplingTable
end I3322
