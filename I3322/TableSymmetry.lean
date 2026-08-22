import I3322.CouplingTable

/-!
# Flipped-transpose symmetrization of coupling tables

The Bell coefficient satisfies `d (-b) (-a) = d a b`.  Consequently a
table can be averaged with its flipped transpose without changing its linear
score.  The geometric-mean part only increases enough to dominate the two
mirror-sector Cauchy--Schwarz bounds arising before symmetrization.
-/

namespace I3322

open scoped BigOperators

namespace CouplingTable

/-- A label set closed under the physical mirror operation `c ↦ -c`. -/
structure Negation (θ : CouplingTable) where
  neg : θ.Label → θ.Label
  involutive : Function.Involutive neg
  label_neg : ∀ c, θ.label (neg c) = -θ.label c

namespace Negation

variable {θ : CouplingTable} (N : θ.Negation)

/-- The mirror operation as an equivalence of the finite label type. -/
def equiv : θ.Label ≃ θ.Label where
  toFun := N.neg
  invFun := N.neg
  left_inv := N.involutive
  right_inv := N.involutive

@[simp] theorem equiv_apply (c : θ.Label) : N.equiv c = N.neg c := rfl

@[simp] theorem neg_neg (c : θ.Label) : N.neg (N.neg c) = c :=
  N.involutive c

/-- Swap the two indices and reflect both scalar labels. -/
def pairEquiv : θ.Label × θ.Label ≃ θ.Label × θ.Label where
  toFun := fun z => (N.neg z.2, N.neg z.1)
  invFun := fun z => (N.neg z.2, N.neg z.1)
  left_inv := by intro z; simp [N.neg_neg]
  right_inv := by intro z; simp [N.neg_neg]

end Negation

theorem d_neg_swap (a b : ℝ) : d (-b) (-a) = d a b := by
  unfold d
  ring

/-- Average a table with the transpose obtained by flipping both labels. -/
noncomputable def symmetrize (θ : CouplingTable) (N : θ.Negation) :
    CouplingTable where
  Label := θ.Label
  label := θ.label
  label_injective := θ.label_injective
  label_mem := θ.label_mem
  weight := fun a b => (θ.weight a b + θ.weight (N.neg b) (N.neg a)) / 2
  weight_nonneg := by
    intro a b
    exact div_nonneg
      (add_nonneg (θ.weight_nonneg a b)
        (θ.weight_nonneg (N.neg b) (N.neg a))) (by norm_num)
  totalWeight := by
    classical
    have hflip :
        (∑ a, ∑ b, θ.weight (N.neg b) (N.neg a)) = 1 := by
      calc
        (∑ a, ∑ b, θ.weight (N.neg b) (N.neg a)) =
            ∑ a, ∑ b, θ.weight b (N.neg a) := by
          apply Fintype.sum_congr
          intro a
          exact N.equiv.sum_comp (fun b => θ.weight b (N.neg a))
        _ = ∑ a, ∑ b, θ.weight b a :=
          N.equiv.sum_comp (fun a => ∑ b, θ.weight b a)
        _ = ∑ a, ∑ b, θ.weight a b := by rw [Finset.sum_comm]
        _ = 1 := θ.totalWeight
    calc
      (∑ a, ∑ b,
          (θ.weight a b + θ.weight (N.neg b) (N.neg a)) / 2) =
          ((∑ a, ∑ b, θ.weight a b) +
            ∑ a, ∑ b, θ.weight (N.neg b) (N.neg a)) / 2 := by
        simp_rw [div_eq_mul_inv, add_mul]
        simp only [Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul]
      _ = 1 := by rw [θ.totalWeight, hflip]; norm_num

@[simp] theorem symmetrize_weight (θ : CouplingTable) (N : θ.Negation)
    (a b : θ.Label) :
    (θ.symmetrize N).weight a b =
      (θ.weight a b + θ.weight (N.neg b) (N.neg a)) / 2 := rfl

theorem symmetrize_row (θ : CouplingTable) (N : θ.Negation) (c : θ.Label) :
    (θ.symmetrize N).row c = (θ.row c + θ.column (N.neg c)) / 2 := by
  classical
  unfold row symmetrize column
  calc
    (∑ b, (θ.weight c b + θ.weight (N.neg b) (N.neg c)) / 2) =
        ((∑ b, θ.weight c b) +
          ∑ b, θ.weight (N.neg b) (N.neg c)) / 2 := by
      simp_rw [div_eq_mul_inv, add_mul]
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul]
    _ = ((∑ b, θ.weight c b) + ∑ b, θ.weight b (N.neg c)) / 2 := by
      have h := N.equiv.sum_comp (fun b => θ.weight b (N.neg c))
      simpa [Negation.equiv] using
        congrArg (fun x => ((∑ b, θ.weight c b) + x) / 2) h

theorem symmetrize_column (θ : CouplingTable) (N : θ.Negation) (c : θ.Label) :
    (θ.symmetrize N).column c = (θ.column c + θ.row (N.neg c)) / 2 := by
  classical
  unfold column symmetrize row
  calc
    (∑ a, (θ.weight a c + θ.weight (N.neg c) (N.neg a)) / 2) =
        ((∑ a, θ.weight a c) +
          ∑ a, θ.weight (N.neg c) (N.neg a)) / 2 := by
      simp_rw [div_eq_mul_inv, add_mul]
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul]
    _ = ((∑ a, θ.weight a c) + ∑ a, θ.weight (N.neg c) a) / 2 := by
      have h := N.equiv.sum_comp (fun a => θ.weight (N.neg c) a)
      simpa [Negation.equiv] using
        congrArg (fun x => ((∑ a, θ.weight a c) + x) / 2) h

/-- The flipped transpose has the same `d`-weighted linear contribution. -/
theorem flipped_linear_eq (θ : CouplingTable) (N : θ.Negation) :
    (∑ a, ∑ b,
        d (θ.label a) (θ.label b) * θ.weight (N.neg b) (N.neg a)) =
      ∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b := by
  classical
  let g : θ.Label × θ.Label → ℝ := fun z =>
    d (θ.label z.1) (θ.label z.2) * θ.weight (N.neg z.2) (N.neg z.1)
  calc
    (∑ a, ∑ b,
        d (θ.label a) (θ.label b) * θ.weight (N.neg b) (N.neg a)) =
        ∑ z, g z := (Fintype.sum_prod_type g).symm
    _ = ∑ z, g (N.pairEquiv z) :=
      (N.pairEquiv.sum_comp g).symm
    _ = ∑ z : θ.Label × θ.Label,
        d (θ.label z.1) (θ.label z.2) * θ.weight z.1 z.2 := by
      apply Fintype.sum_congr
      intro z
      simp only [g, Negation.pairEquiv, Equiv.coe_fn_mk]
      rw [N.label_neg, N.label_neg, N.neg_neg, N.neg_neg, d_neg_swap]
    _ = ∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b :=
      Fintype.sum_prod_type (fun z : θ.Label × θ.Label =>
        d (θ.label z.1) (θ.label z.2) * θ.weight z.1 z.2)

/-- Symmetrization leaves the linear part of the table score unchanged. -/
theorem symmetrize_linear_eq (θ : CouplingTable) (N : θ.Negation) :
    (∑ a, ∑ b,
        d ((θ.symmetrize N).label a) ((θ.symmetrize N).label b) *
          (θ.symmetrize N).weight a b) =
      ∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b := by
  classical
  change
    (∑ a : θ.Label, ∑ b : θ.Label,
      d (θ.label a) (θ.label b) *
        ((θ.weight a b + θ.weight (N.neg b) (N.neg a)) / 2)) = _
  have hpoint (a b : θ.Label) :
      d (θ.label a) (θ.label b) *
          ((θ.weight a b + θ.weight (N.neg b) (N.neg a)) / 2) =
        (d (θ.label a) (θ.label b) * θ.weight a b +
          d (θ.label a) (θ.label b) *
            θ.weight (N.neg b) (N.neg a)) / 2 := by ring
  calc
    _ = ((∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
        ∑ a, ∑ b, d (θ.label a) (θ.label b) *
          θ.weight (N.neg b) (N.neg a)) / 2 := by
      simp_rw [hpoint, div_eq_mul_inv, add_mul]
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul]
    _ = _ := by rw [θ.flipped_linear_eq N]; ring

/-- Scalar AM--GM inequality used for the mirror-sector symmetrization. -/
theorem sqrt_average_mul_average_ge (R Rm C Cm : ℝ)
    (hR : 0 ≤ R) (hRm : 0 ≤ Rm) (hC : 0 ≤ C) (hCm : 0 ≤ Cm) :
    (Real.sqrt (R * Rm) + Real.sqrt (C * Cm)) / 2 ≤
      Real.sqrt (((R + Cm) / 2) * ((C + Rm) / 2)) := by
  have hxarg : 0 ≤ R * Rm := mul_nonneg hR hRm
  have hyarg : 0 ≤ C * Cm := mul_nonneg hC hCm
  have huarg : 0 ≤ R * C := mul_nonneg hR hC
  have hvarg : 0 ≤ Cm * Rm := mul_nonneg hCm hRm
  have htargetarg : 0 ≤ ((R + Cm) / 2) * ((C + Rm) / 2) :=
    mul_nonneg (div_nonneg (add_nonneg hR hCm) (by norm_num))
      (div_nonneg (add_nonneg hC hRm) (by norm_num))
  rw [Real.le_sqrt (by positivity) htargetarg]
  have hx := Real.sq_sqrt hxarg
  have hy := Real.sq_sqrt hyarg
  have hu := Real.sq_sqrt huarg
  have hv := Real.sq_sqrt hvarg
  have hxyuv : Real.sqrt (R * Rm) * Real.sqrt (C * Cm) =
      Real.sqrt (R * C) * Real.sqrt (Cm * Rm) := by
    have hxy : 0 ≤ Real.sqrt (R * Rm) * Real.sqrt (C * Cm) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have huv : 0 ≤ Real.sqrt (R * C) * Real.sqrt (Cm * Rm) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  nlinarith [hxyuv,
    sq_nonneg (Real.sqrt (R * C) - Real.sqrt (Cm * Rm))]

/-- The nonlinear part of the symmetrized table dominates the average of
the Alice and Bob mirror-sector contributions. -/
theorem mirror_terms_le_symmetrize (θ : CouplingTable) (N : θ.Negation) :
    (∑ c, s (θ.label c) *
        (Real.sqrt (θ.row c * θ.row (N.neg c)) +
          Real.sqrt (θ.column c * θ.column (N.neg c))) / 2) ≤
      ∑ c, s ((θ.symmetrize N).label c) *
        Real.sqrt ((θ.symmetrize N).row c *
          (θ.symmetrize N).column c) := by
  apply Finset.sum_le_sum
  intro c _
  rw [symmetrize_row, symmetrize_column]
  change s (θ.label c) *
      (Real.sqrt (θ.row c * θ.row (N.neg c)) +
        Real.sqrt (θ.column c * θ.column (N.neg c))) / 2 ≤
    s (θ.label c) *
      Real.sqrt (((θ.row c + θ.column (N.neg c)) / 2) *
        ((θ.column c + θ.row (N.neg c)) / 2))
  calc
    _ = s (θ.label c) *
        ((Real.sqrt (θ.row c * θ.row (N.neg c)) +
          Real.sqrt (θ.column c * θ.column (N.neg c))) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sqrt_average_mul_average_ge _ _ _ _
        (θ.row_nonneg c) (θ.row_nonneg (N.neg c))
        (θ.column_nonneg c) (θ.column_nonneg (N.neg c)))
      (Real.sqrt_nonneg _)

/-- The raw two-party spectral bound before table symmetrization. -/
noncomputable def mirrorScore (θ : CouplingTable) (N : θ.Negation) : ℝ :=
  (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
    ∑ c, s (θ.label c) *
      (Real.sqrt (θ.row c * θ.row (N.neg c)) +
        Real.sqrt (θ.column c * θ.column (N.neg c))) / 2

/-- The ordinary coupling-table score of the symmetrized table dominates the
raw mirror-sector score. -/
theorem mirrorScore_le_symmetrize_score (θ : CouplingTable) (N : θ.Negation) :
    θ.mirrorScore N ≤ (θ.symmetrize N).score := by
  unfold mirrorScore score
  rw [θ.symmetrize_linear_eq N]
  exact add_le_add (le_refl _) (θ.mirror_terms_le_symmetrize N)

end CouplingTable
end I3322
