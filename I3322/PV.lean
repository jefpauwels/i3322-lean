import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt

/-!
# Finite Pal--Vertesi chains

This file is the direct Lean encoding of equations (4)--(7) in the
manuscript.  Amplitudes are indexed from `0` in Lean, so `amplitude i`
corresponds to the paper's `lambda_(i+1)`.
-/

namespace I3322

/-- The coefficient `s(c) = sqrt (1 - c^2)` from equation (4). -/
noncomputable def s (c : ℝ) : ℝ :=
  Real.sqrt (1 - c ^ 2)

/-- The coefficient `d(a,b) = ab + (a-b)/2 - 1` from equation (4). -/
noncomputable def d (a b : ℝ) : ℝ :=
  a * b + (a - b) / 2 - 1

/--
A finite PV chain.  Only entries in the displayed finite ranges matter;
the functions are used to keep index arithmetic transparent.
-/
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

/-- The denominator of equation (5). -/
noncomputable def normSq (p : PVChain) : ℝ :=
  ∑ i ∈ Finset.range p.n, p.amplitude i ^ 2

/-- The numerator of equation (5), in zero-based indexing. -/
noncomputable def numerator (p : PVChain) : ℝ :=
  (∑ i ∈ Finset.range p.n,
      d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2) +
    ∑ i ∈ Finset.range (p.n - 1),
      s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)

/-- The finite PV value `P_n(c,lambda)` from equation (5). -/
noncomputable def value (p : PVChain) : ℝ :=
  p.numerator / p.normSq

theorem normSq_pos' (p : PVChain) : 0 < p.normSq :=
  p.normSq_pos

theorem normSq_ne_zero (p : PVChain) : p.normSq ≠ 0 :=
  ne_of_gt p.normSq_pos'

/-- `normSq` written as a sum over the finite type `Fin p.n`. -/
theorem normSq_eq_fin_sum (p : PVChain) :
    p.normSq = ∑ i : Fin p.n, p.amplitude i ^ 2 := by
  exact Finset.sum_range _

/-- The PV numerator written with finite-type sums. -/
theorem numerator_eq_fin_sums (p : PVChain) :
    p.numerator =
      (∑ i : Fin p.n,
        d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2) +
      ∑ i : Fin (p.n - 1),
        s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1) := by
  unfold numerator
  rw [Finset.sum_range, Finset.sum_range]

end PVChain

/-- The supremum of the values of all finite PV chains. -/
noncomputable def betaPV : ℝ :=
  sSup (Set.range PVChain.value)

end I3322
