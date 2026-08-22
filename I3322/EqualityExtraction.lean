import I3322.TableToPV
import I3322.EqualityChain
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.List.Chain
import I3322.ChainStationarity
import I3322.FiniteSpine

/-!
# Equality-table rigidity

This file isolates the finite-table part of the nonattainment argument.  In
particular, it records the exact first-variation coefficients (the ``cell
gains'' of the paper), proves that their weighted average is the table score,
and formalizes the crossed-cell argument which makes the positive support a
monotone relation.

The definitions use `sqrt (R*C) / R` rather than `sqrt (C/R)`.  They agree
whenever `R > 0`, while the former has the correct value `0` when the opposite
marginal vanishes and is substantially safer at boundary points.
-/

namespace I3322
namespace CouplingTable

open scoped BigOperators

/-- Coefficient of an infinitesimal increase of row `c` in the square-root
part of the table score. -/
noncomputable def leftSlope (θ : CouplingTable) (c : θ.Label) : ℝ :=
  if θ.row c = 0 then 0
  else s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / (2 * θ.row c)

/-- Coefficient of an infinitesimal increase of column `c` in the square-root
part of the table score. -/
noncomputable def rightSlope (θ : CouplingTable) (c : θ.Label) : ℝ :=
  if θ.column c = 0 then 0
  else s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / (2 * θ.column c)

/-- The one-cell first variation used in the equality case. -/
noncomputable def gain (θ : CouplingTable) (a b : θ.Label) : ℝ :=
  d (θ.label a) (θ.label b) + θ.leftSlope a + θ.rightSlope b

/-- Kronecker point mass, kept behind a definition so theorem statements do
not require a computational `DecidableEq` instance on the label type. -/
noncomputable def point (θ : CouplingTable) (a c : θ.Label) : ℝ := by
  classical
  exact if c = a then 1 else 0

@[simp] theorem point_self (θ : CouplingTable) (a : θ.Label) : θ.point a a = 1 := by
  simp [point]

theorem point_of_ne (θ : CouplingTable) {a c : θ.Label} (h : c ≠ a) :
    θ.point a c = 0 := by
  simp [point, h]

theorem point_nonneg (θ : CouplingTable) (a c : θ.Label) : 0 ≤ θ.point a c := by
  classical
  simp only [point]
  split <;> norm_num

theorem sum_point (θ : CouplingTable) (a : θ.Label) : ∑ c, θ.point a c = 1 := by
  classical
  simp [point]

/-- Change one label while leaving the coupling weights fixed.  The explicit
freshness premise is what is needed near a boundary label; it will later be
obtained uniformly from finiteness. -/
noncomputable def relabelAt (θ : CouplingTable) (c : θ.Label) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hfresh : ∀ k, k ≠ c → x ≠ θ.label k) : CouplingTable := by
  classical
  refine
    { Label := θ.Label
      label := fun k => if k = c then x else θ.label k
      label_injective := ?_
      label_mem := ?_
      weight := θ.weight
      weight_nonneg := θ.weight_nonneg
      totalWeight := θ.totalWeight }
  · intro a b hab
    by_cases ha : a = c
    · subst a
      by_cases hb : b = c
      · exact hb.symm
      · exfalso
        exact hfresh b hb (by simpa [hb] using hab)
    · by_cases hb : b = c
      · subst b
        exfalso
        exact hfresh a ha (by simpa [ha] using hab.symm)
      · apply θ.label_injective
        simpa [ha, hb] using hab
  · intro k
    by_cases hk : k = c
    · simpa [hk] using hx
    · simpa [hk] using θ.label_mem k

@[simp] theorem relabelAt_label_self (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx) (hfresh) :
    (θ.relabelAt c x hx hfresh).label c = x := by
  simp [relabelAt]

theorem relabelAt_label_of_ne (θ : CouplingTable) (c k : θ.Label)
    (x : ℝ) (hx) (hfresh) (hk : k ≠ c) :
    (θ.relabelAt c x hx hfresh).label k = θ.label k := by
  simp [relabelAt, hk]

@[simp] theorem relabelAt_weight (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx) (hfresh) (a b : θ.Label) :
    (θ.relabelAt c x hx hfresh).weight a b = θ.weight a b := rfl

@[simp] theorem relabelAt_row (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx) (hfresh) (a : θ.Label) :
    (θ.relabelAt c x hx hfresh).row a = θ.row a := rfl

@[simp] theorem relabelAt_column (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx) (hfresh) (b : θ.Label) :
    (θ.relabelAt c x hx hfresh).column b = θ.column b := rfl

/-- Move a fraction `t` of a table to the point mass in cell `(a,b)`. -/
noncomputable def spike (θ : CouplingTable) (a b : θ.Label) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : CouplingTable := by
  classical
  exact
    { Label := θ.Label
      label := θ.label
      label_injective := θ.label_injective
      label_mem := θ.label_mem
      weight := fun i j => (1 - t) * θ.weight i j +
        t * (θ.point a i * θ.point b j)
      weight_nonneg := fun i j => add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1) (θ.weight_nonneg i j))
        (mul_nonneg ht0 (mul_nonneg (θ.point_nonneg a i) (θ.point_nonneg b j)))
      totalWeight := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [θ.totalWeight]
        simp [point] }

theorem spike_row (θ : CouplingTable) (a b : θ.Label) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : θ.Label) :
    (θ.spike a b t ht0 ht1).row c =
      (1 - t) * θ.row c + t * θ.point a c := by
  classical
  unfold row spike
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  by_cases hca : c = a
  · subst c
    simp [sum_point]
  · simp [point_of_ne θ hca]

theorem spike_column (θ : CouplingTable) (a b : θ.Label) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : θ.Label) :
    (θ.spike a b t ht0 ht1).column c =
      (1 - t) * θ.column c + t * θ.point b c := by
  classical
  unfold column spike
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  by_cases hcb : c = b
  · subst c
    simp [sum_point]
  · simp [point_of_ne θ hcb]

/-- The score along the affine segment from `θ` to a point mass.  This is
defined for every real parameter; on `[0,1]` it is the score of `spike`. -/
noncomputable def spikeScore (θ : CouplingTable) (a b : θ.Label) (t : ℝ) : ℝ :=
  by
    classical
    exact
      (1 - t) * θ.diagonalPart + t * d (θ.label a) (θ.label b) +
        ∑ c, s (θ.label c) * Real.sqrt
          (((1 - t) * θ.row c + t * θ.point a c) *
            ((1 - t) * θ.column c + t * θ.point b c))

theorem spike_diagonalPart (θ : CouplingTable) (a b : θ.Label) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (θ.spike a b t ht0 ht1).diagonalPart =
      (1 - t) * θ.diagonalPart + t * d (θ.label a) (θ.label b) := by
  classical
  unfold diagonalPart spike
  change (∑ i, ∑ j, d (θ.label i) (θ.label j) *
      ((1 - t) * θ.weight i j + t * (θ.point a i * θ.point b j))) = _
  have hbase :
      (∑ i, ∑ j, d (θ.label i) (θ.label j) *
        ((1 - t) * θ.weight i j)) =
      (1 - t) * ∑ i, ∑ j, d (θ.label i) (θ.label j) * θ.weight i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoint :
      (∑ i, ∑ j, d (θ.label i) (θ.label j) *
        (t * (θ.point a i * θ.point b j))) =
      t * d (θ.label a) (θ.label b) := by
    simp [point]
    ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hbase, hpoint]

theorem score_spike_eq_spikeScore (θ : CouplingTable) (a b : θ.Label) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (θ.spike a b t ht0 ht1).score = θ.spikeScore a b t := by
  classical
  rw [score_eq_parts]
  rw [spike_diagonalPart]
  unfold junctionPart spikeScore
  simp_rw [spike_row, spike_column]
  rfl

@[simp] theorem spikeScore_zero (θ : CouplingTable) (a b : θ.Label) :
    θ.spikeScore a b 0 = θ.score := by
  classical
  simp [spikeScore, score_eq_parts, junctionPart]

/-- Per-label derivative of the square-root part along a spike segment. -/
noncomputable def junctionSlopeTerm (θ : CouplingTable) (a b c : θ.Label) : ℝ :=
  -s (θ.label c) * Real.sqrt (θ.row c * θ.column c) +
    θ.point a c * θ.leftSlope c + θ.point b c * θ.rightSlope c

theorem sum_junctionSlopeTerm (θ : CouplingTable) (a b : θ.Label) :
    (∑ c, θ.junctionSlopeTerm a b c) =
      -θ.junctionPart + θ.leftSlope a + θ.rightSlope b := by
  classical
  unfold junctionSlopeTerm junctionPart
  simp_rw [Finset.sum_add_distrib]
  have hleft : ∑ c, θ.point a c * θ.leftSlope c = θ.leftSlope a := by
    simp [point]
  have hright : ∑ c, θ.point b c * θ.rightSlope c = θ.rightSlope b := by
    simp [point]
  rw [hleft, hright]
  congr 2
  calc
    (∑ c, -s (θ.label c) * Real.sqrt (θ.row c * θ.column c)) =
        ∑ c, -(s (θ.label c) * Real.sqrt (θ.row c * θ.column c)) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = -(∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c)) := by
      simpa only using (Finset.sum_neg_distrib (s := Finset.univ)
        (fun c => s (θ.label c) * Real.sqrt (θ.row c * θ.column c)))

/-- The square-root summand is differentiable in every spike direction whose
source row and target column are positive.  Marginals which vanish elsewhere
give identically zero summands, so no derivative of `sqrt` at zero is used. -/
theorem hasDerivAt_spikeJunctionTerm (θ : CouplingTable) (a b c : θ.Label)
    (hRa : 0 < θ.row a) (hCb : 0 < θ.column b) :
    HasDerivAt
      (fun t : ℝ => s (θ.label c) * Real.sqrt
        (((1 - t) * θ.row c + t * θ.point a c) *
          ((1 - t) * θ.column c + t * θ.point b c)))
      (θ.junctionSlopeTerm a b c) 0 := by
  classical
  by_cases hR : θ.row c = 0
  · have hca : c ≠ a := by
      intro h
      subst c
      linarith
    have hp : θ.point a c = 0 := θ.point_of_ne hca
    have hslope : θ.junctionSlopeTerm a b c = 0 := by
      simp [junctionSlopeTerm, hR, hp, leftSlope, rightSlope]
    rw [hslope]
    simpa [hR, hp] using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  by_cases hC : θ.column c = 0
  · have hcb : c ≠ b := by
      intro h
      subst c
      linarith
    have hp : θ.point b c = 0 := θ.point_of_ne hcb
    have hslope : θ.junctionSlopeTerm a b c = 0 := by
      simp [junctionSlopeTerm, hC, hp, leftSlope, rightSlope]
    rw [hslope]
    simpa [hC, hp] using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  have hRpos : 0 < θ.row c := lt_of_le_of_ne (θ.row_nonneg c) (Ne.symm hR)
  have hCpos : 0 < θ.column c := lt_of_le_of_ne (θ.column_nonneg c) (Ne.symm hC)
  have hrow : HasDerivAt
      (fun t : ℝ => (1 - t) * θ.row c + t * θ.point a c)
      (θ.point a c - θ.row c) 0 := by
    have h := (((hasDerivAt_id (𝕜 := ℝ) 0).const_sub (1 : ℝ)).mul_const
      (θ.row c)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (θ.point a c))
    change HasDerivAt (fun t : ℝ => (1 - t) * θ.row c + t * θ.point a c)
      ((-1) * θ.row c + 1 * θ.point a c) 0 at h
    exact h.congr_deriv (by ring)
  have hcolumn : HasDerivAt
      (fun t : ℝ => (1 - t) * θ.column c + t * θ.point b c)
      (θ.point b c - θ.column c) 0 := by
    have h := (((hasDerivAt_id (𝕜 := ℝ) 0).const_sub (1 : ℝ)).mul_const
      (θ.column c)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (θ.point b c))
    change HasDerivAt (fun t : ℝ => (1 - t) * θ.column c + t * θ.point b c)
      ((-1) * θ.column c + 1 * θ.point b c) 0 at h
    exact h.congr_deriv (by ring)
  have hprod := hrow.mul hcolumn
  have hRC :
      ((fun t : ℝ => (1 - t) * θ.row c + t * θ.point a c) *
        (fun t : ℝ => (1 - t) * θ.column c + t * θ.point b c)) 0 ≠ 0 := by
    simp
    exact ⟨hR, hC⟩
  have hsqrt := hprod.sqrt hRC
  have hmul := hsqrt.const_mul (s (θ.label c))
  have hslope : θ.junctionSlopeTerm a b c =
      s (θ.label c) *
        (((θ.point a c - θ.row c) * θ.column c +
          θ.row c * (θ.point b c - θ.column c)) /
            (2 * Real.sqrt (θ.row c * θ.column c))) := by
    unfold junctionSlopeTerm leftSlope rightSlope
    rw [if_neg hR, if_neg hC]
    have hsquare : Real.sqrt (θ.row c * θ.column c) ^ 2 =
        θ.row c * θ.column c := Real.sq_sqrt (mul_nonneg (θ.row_nonneg c) (θ.column_nonneg c))
    have hsqrtne : Real.sqrt (θ.row c * θ.column c) ≠ 0 := by positivity
    field_simp
    rw [hsquare]
    ring
  rw [hslope]
  norm_num at hmul ⊢
  exact hmul

/-- Exact first derivative of the table score along a point-mass spike. -/
theorem hasDerivAt_spikeScore (θ : CouplingTable) (a b : θ.Label)
    (hRa : 0 < θ.row a) (hCb : 0 < θ.column b) :
    HasDerivAt (θ.spikeScore a b) (θ.gain a b - θ.score) 0 := by
  classical
  have hdiag : HasDerivAt
      (fun t : ℝ => (1 - t) * θ.diagonalPart +
        t * d (θ.label a) (θ.label b))
      (d (θ.label a) (θ.label b) - θ.diagonalPart) 0 := by
    have h := (((hasDerivAt_id (𝕜 := ℝ) 0).const_sub (1 : ℝ)).mul_const
      θ.diagonalPart).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (d (θ.label a) (θ.label b)))
    change HasDerivAt
      (fun t : ℝ => (1 - t) * θ.diagonalPart + t * d (θ.label a) (θ.label b))
      ((-1) * θ.diagonalPart + 1 * d (θ.label a) (θ.label b)) 0 at h
    exact h.congr_deriv (by ring)
  have hjunction : HasDerivAt
      (fun t : ℝ => ∑ c, s (θ.label c) * Real.sqrt
        (((1 - t) * θ.row c + t * θ.point a c) *
          ((1 - t) * θ.column c + t * θ.point b c)))
      (∑ c, θ.junctionSlopeTerm a b c) 0 := by
    exact HasDerivAt.fun_sum (u := Finset.univ)
      (fun c _ => θ.hasDerivAt_spikeJunctionTerm a b c hRa hCb)
  have hsum := hdiag.add hjunction
  change HasDerivAt
    (fun t : ℝ =>
      ((1 - t) * θ.diagonalPart + t * d (θ.label a) (θ.label b)) +
      ∑ c, s (θ.label c) * Real.sqrt
        (((1 - t) * θ.row c + t * θ.point a c) *
          ((1 - t) * θ.column c + t * θ.point b c)))
    (θ.gain a b - θ.score) 0
  have hslope : θ.gain a b - θ.score =
      d (θ.label a) (θ.label b) - θ.diagonalPart +
        ∑ c, θ.junctionSlopeTerm a b c := by
    rw [sum_junctionSlopeTerm]
    unfold gain
    rw [score_eq_parts]
    ring
  rw [hslope]
  exact hsum

/-- At an equality table, the gain of every direction with a positive source
row and positive target column is at most the optimum. -/
theorem gain_le_betaPV (θ : CouplingTable) (hscore : θ.score = betaPV)
    (a b : θ.Label) (hRa : 0 < θ.row a) (hCb : 0 < θ.column b) :
    θ.gain a b ≤ betaPV := by
  have hmax : IsMaxOn (θ.spikeScore a b) (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    have hbound := Ensemble.score_le_betaPV
      (θ.spike a b t ht.1 ht.2)
    rw [score_spike_eq_spikeScore] at hbound
    simpa [spikeScore_zero, hscore] using hbound
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset
      (x := (0 : ℝ)) (y := (1 : ℝ))
      (s := Set.Icc (0 : ℝ) 1) (by
        rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)])
    simpa using h
  have hderiv := θ.hasDerivAt_spikeScore a b hRa hCb
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    (hasDerivWithinAt_iff_hasFDerivWithinAt.mp hderiv.hasDerivWithinAt)
    htangent
  have hslope : θ.gain a b - θ.score ≤ 0 := by
    simpa using hnonpos
  linarith

theorem row_eq_zero_iff (θ : CouplingTable) (a : θ.Label) :
    θ.row a = 0 ↔ ∀ b, θ.weight a b = 0 := by
  constructor
  · intro h b
    have hle : θ.weight a b ≤ θ.row a := by
      unfold row
      exact Finset.single_le_sum (fun j _ => θ.weight_nonneg a j) (Finset.mem_univ b)
    exact le_antisymm (by simpa [h] using hle) (θ.weight_nonneg a b)
  · intro h
    simp [row, h]

theorem column_eq_zero_iff (θ : CouplingTable) (b : θ.Label) :
    θ.column b = 0 ↔ ∀ a, θ.weight a b = 0 := by
  constructor
  · intro h a
    have hle : θ.weight a b ≤ θ.column b := by
      unfold column
      exact Finset.single_le_sum (fun i _ => θ.weight_nonneg i b) (Finset.mem_univ a)
    exact le_antisymm (by simpa [h] using hle) (θ.weight_nonneg a b)
  · intro h
    simp [column, h]

theorem row_pos_of_weight_pos (θ : CouplingTable) {a b : θ.Label}
    (h : 0 < θ.weight a b) : 0 < θ.row a := by
  exact lt_of_lt_of_le h (by
    unfold row
    exact Finset.single_le_sum (fun j _ => θ.weight_nonneg a j) (Finset.mem_univ b))

theorem column_pos_of_weight_pos (θ : CouplingTable) {a b : θ.Label}
    (h : 0 < θ.weight a b) : 0 < θ.column b := by
  exact lt_of_lt_of_le h (by
    unfold column
    exact Finset.single_le_sum (fun i _ => θ.weight_nonneg i b) (Finset.mem_univ a))

theorem row_mul_leftSlope (θ : CouplingTable) (c : θ.Label) :
    θ.row c * θ.leftSlope c =
      s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2 := by
  by_cases hR : θ.row c = 0
  · simp [leftSlope, hR]
  · rw [leftSlope, if_neg hR]
    field_simp

theorem column_mul_rightSlope (θ : CouplingTable) (c : θ.Label) :
    θ.column c * θ.rightSlope c =
      s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2 := by
  by_cases hC : θ.column c = 0
  · simp [rightSlope, hC]
  · rw [rightSlope, if_neg hC]
    field_simp

/-- Euler's identity for the homogeneous square-root term: the table-weighted
average of the cell gains is exactly the table score. -/
theorem sum_weight_mul_gain (θ : CouplingTable) :
    (∑ a, ∑ b, θ.weight a b * θ.gain a b) = θ.score := by
  classical
  unfold gain score
  have hdiag :
      (∑ a, ∑ b, θ.weight a b * d (θ.label a) (θ.label b)) =
        ∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hleft :
      (∑ a, ∑ b, θ.weight a b * θ.leftSlope a) =
        ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_mul]
    change θ.row a * θ.leftSlope a = _
    exact θ.row_mul_leftSlope a
  have hright :
      (∑ a, ∑ b, θ.weight a b * θ.rightSlope b) =
        ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_mul]
    change θ.column b * θ.rightSlope b = _
    exact θ.column_mul_rightSlope b
  calc
    (∑ a, ∑ b, θ.weight a b *
        (d (θ.label a) (θ.label b) + θ.leftSlope a + θ.rightSlope b)) =
        (∑ a, ∑ b, θ.weight a b * d (θ.label a) (θ.label b)) +
        (∑ a, ∑ b, θ.weight a b * θ.leftSlope a) +
        (∑ a, ∑ b, θ.weight a b * θ.rightSlope b) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
        (∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2) +
        (∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2) := by
      rw [hdiag, hleft, hright]
    _ = (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
        ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) := by
      have hjunction :
          (∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2) +
              (∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) / 2) =
            ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
      rw [add_assoc, hjunction]

/-- If every cell gain is bounded by `betaPV`, equality of the table score
forces every occupied cell to be tight. -/
theorem occupied_tight_of_cellBound (θ : CouplingTable)
    (hscore : θ.score = betaPV)
    (hcell : ∀ a b, θ.gain a b ≤ betaPV) {a b : θ.Label}
    (hab : 0 < θ.weight a b) : θ.gain a b = betaPV := by
  by_contra hne
  have hstrict : θ.gain a b < betaPV := lt_of_le_of_ne (hcell a b) hne
  have hsum :
      (∑ i, ∑ j, θ.weight i j * θ.gain i j) <
        ∑ i, ∑ j, θ.weight i j * betaPV := by
    apply Finset.sum_lt_sum
    · intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hcell i j) (θ.weight_nonneg i j)
    · refine ⟨a, Finset.mem_univ a, ?_⟩
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_mul_of_nonneg_left (hcell a j) (θ.weight_nonneg a j)
      · exact ⟨b, Finset.mem_univ b,
          mul_lt_mul_of_pos_left hstrict hab⟩
  rw [sum_weight_mul_gain, hscore] at hsum
  simp_rw [← Finset.sum_mul] at hsum
  rw [θ.totalWeight] at hsum
  simp at hsum

/-- Every positive cell of an equality table is tight.  Unlike the auxiliary
version above, this theorem derives the required cell bounds from the actual
one-sided variations and makes no assumption about unused rows or columns. -/
theorem occupied_tight (θ : CouplingTable) (hscore : θ.score = betaPV)
    {a b : θ.Label} (hab : 0 < θ.weight a b) : θ.gain a b = betaPV := by
  have hbound : θ.gain a b ≤ betaPV := θ.gain_le_betaPV hscore a b
    (θ.row_pos_of_weight_pos hab) (θ.column_pos_of_weight_pos hab)
  by_contra hne
  have hstrict : θ.gain a b < betaPV := lt_of_le_of_ne hbound hne
  have hsum :
      (∑ i, ∑ j, θ.weight i j * θ.gain i j) <
        ∑ i, ∑ j, θ.weight i j * betaPV := by
    apply Finset.sum_lt_sum
    · intro i _
      apply Finset.sum_le_sum
      intro j _
      rcases (θ.weight_nonneg i j).eq_or_lt with hzero | hpos
      · rw [← hzero]
        simp
      · exact mul_le_mul_of_nonneg_left
          (θ.gain_le_betaPV hscore i j
            (θ.row_pos_of_weight_pos hpos) (θ.column_pos_of_weight_pos hpos))
          (θ.weight_nonneg i j)
    · refine ⟨a, Finset.mem_univ a, ?_⟩
      apply Finset.sum_lt_sum
      · intro j _
        rcases (θ.weight_nonneg a j).eq_or_lt with hzero | hpos
        · rw [← hzero]
          simp
        · exact mul_le_mul_of_nonneg_left
            (θ.gain_le_betaPV hscore a j
              (θ.row_pos_of_weight_pos hpos) (θ.column_pos_of_weight_pos hpos))
            (θ.weight_nonneg a j)
      · exact ⟨b, Finset.mem_univ b, mul_lt_mul_of_pos_left hstrict hab⟩
  rw [sum_weight_mul_gain, hscore] at hsum
  simp_rw [← Finset.sum_mul] at hsum
  rw [θ.totalWeight] at hsum
  simp at hsum

/-- The mixed second difference of `d` is exactly the product appearing in
the crossed-cell argument. -/
theorem d_cross_difference (a a' b b' : ℝ) :
    d a b' + d a' b - (d a b + d a' b') = (a - a') * (b' - b) := by
  unfold d
  ring

/-- Tight occupied cells and the upper gain bound make the positive support
a monotone relation on the ordered real labels. -/
theorem occupied_ordered_of_cellBound (θ : CouplingTable)
    (hscore : θ.score = betaPV)
    (hcell : ∀ a b, θ.gain a b ≤ betaPV)
    {a a' b b' : θ.Label}
    (hab : 0 < θ.weight a b) (ha'b' : 0 < θ.weight a' b')
    (haa' : θ.label a < θ.label a') : θ.label b ≤ θ.label b' := by
  have habtight : θ.gain a b = betaPV :=
    θ.occupied_tight_of_cellBound hscore hcell hab
  have ha'b'tight : θ.gain a' b' = betaPV :=
    θ.occupied_tight_of_cellBound hscore hcell ha'b'
  have hcross1 := hcell a b'
  have hcross2 := hcell a' b
  unfold gain at habtight ha'b'tight hcross1 hcross2
  have hprod :
      (θ.label a - θ.label a') * (θ.label b' - θ.label b) ≤ 0 := by
    rw [← d_cross_difference]
    linarith
  by_contra hnot
  have hbb' : θ.label b' < θ.label b := lt_of_not_ge hnot
  have : 0 < (θ.label a - θ.label a') * (θ.label b' - θ.label b) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr haa') (sub_neg.mpr hbb')
  linarith

/-- Crossed-cell monotonicity for an equality table. -/
theorem occupied_ordered (θ : CouplingTable) (hscore : θ.score = betaPV)
    {a a' b b' : θ.Label}
    (hab : 0 < θ.weight a b) (ha'b' : 0 < θ.weight a' b')
    (haa' : θ.label a < θ.label a') : θ.label b ≤ θ.label b' := by
  have habtight : θ.gain a b = betaPV := θ.occupied_tight hscore hab
  have ha'b'tight : θ.gain a' b' = betaPV := θ.occupied_tight hscore ha'b'
  have hcross1 : θ.gain a b' ≤ betaPV := θ.gain_le_betaPV hscore a b'
    (θ.row_pos_of_weight_pos hab) (θ.column_pos_of_weight_pos ha'b')
  have hcross2 : θ.gain a' b ≤ betaPV := θ.gain_le_betaPV hscore a' b
    (θ.row_pos_of_weight_pos ha'b') (θ.column_pos_of_weight_pos hab)
  unfold gain at habtight ha'b'tight hcross1 hcross2
  have hprod :
      (θ.label a - θ.label a') * (θ.label b' - θ.label b) ≤ 0 := by
    rw [← d_cross_difference]
    linarith
  by_contra hnot
  have hbb' : θ.label b' < θ.label b := lt_of_not_ge hnot
  have : 0 < (θ.label a - θ.label a') * (θ.label b' - θ.label b) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr haa') (sub_neg.mpr hbb')
  linarith

/-- A strictly increasing occupied edge. -/
def IncreasingEdge (θ : CouplingTable) (a b : θ.Label) : Prop :=
  0 < θ.weight a b ∧ θ.label a < θ.label b

/-- Reachability by strictly increasing occupied edges. -/
def IncreasingReach (θ : CouplingTable) (start finish : θ.Label) : Prop :=
  Relation.ReflTransGen θ.IncreasingEdge start finish

/-- Moving one step to an off-diagonal predecessor.  The order condition is
oriented in the direction in which the predecessor path is traversed. -/
def DecreasingPredecessorEdge (θ : CouplingTable) (current predecessor : θ.Label) : Prop :=
  0 < θ.weight predecessor current ∧ θ.label predecessor < θ.label current

/-- Reachability while following off-diagonal predecessors to the left. -/
def DecreasingPredecessorReach (θ : CouplingTable) (start finish : θ.Label) : Prop :=
  Relation.ReflTransGen θ.DecreasingPredecessorEdge start finish

/-- A strictly decreasing occupied edge. -/
def DecreasingEdge (θ : CouplingTable) (a b : θ.Label) : Prop :=
  0 < θ.weight a b ∧ θ.label b < θ.label a

def DecreasingReach (θ : CouplingTable) (start finish : θ.Label) : Prop :=
  Relation.ReflTransGen θ.DecreasingEdge start finish

/-- Follow predecessors of a decreasing path; their labels strictly increase. -/
def IncreasingPredecessorEdge (θ : CouplingTable) (current predecessor : θ.Label) : Prop :=
  0 < θ.weight predecessor current ∧ θ.label current < θ.label predecessor

def IncreasingPredecessorReach (θ : CouplingTable) (start finish : θ.Label) : Prop :=
  Relation.ReflTransGen θ.IncreasingPredecessorEdge start finish

/-- Starting with an increasing occupied edge, finite monotonicity produces a
reachable sink: it has a strictly increasing occupied edge entering it and no
off-diagonal occupied edge leaving it. -/
theorem exists_occupied_sink (θ : CouplingTable) (hscore : θ.score = betaPV)
    {a b : θ.Label} (hab : 0 < θ.weight a b)
    (hlt : θ.label a < θ.label b) :
    ∃ sink pred,
      θ.IncreasingReach b sink ∧
      0 < θ.weight pred sink ∧ θ.label pred < θ.label sink ∧
      ∀ z, z ≠ sink → θ.weight sink z = 0 := by
  classical
  let reachable : Finset θ.Label :=
    Finset.univ.filter (fun x => θ.IncreasingReach b x)
  have hnonempty : reachable.Nonempty := by
    refine ⟨b, ?_⟩
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨sink, hsinkMem, hsinkMax⟩ :=
    Finset.exists_max_image reachable θ.label hnonempty
  have hsinkReach : θ.IncreasingReach b sink := by
    simpa [reachable] using hsinkMem
  have hincoming : ∃ pred,
      0 < θ.weight pred sink ∧ θ.label pred < θ.label sink := by
    rcases Relation.ReflTransGen.cases_tail hsinkReach with heq | htail
    · subst sink
      exact ⟨a, hab, hlt⟩
    · obtain ⟨pred, _, hpred⟩ := htail
      exact ⟨pred, hpred.1, hpred.2⟩
  obtain ⟨pred, hpredWeight, hpredLt⟩ := hincoming
  refine ⟨sink, pred, hsinkReach, hpredWeight, hpredLt, ?_⟩
  intro z hzsink
  apply le_antisymm
  · by_contra hnot
    have hout : 0 < θ.weight sink z := lt_of_not_ge hnot
    have hle : θ.label sink ≤ θ.label z :=
      θ.occupied_ordered hscore hpredWeight hout hpredLt
    have hlabelNe : θ.label sink ≠ θ.label z := by
      intro heq
      exact hzsink (θ.label_injective heq).symm
    have hsinkz : θ.label sink < θ.label z := lt_of_le_of_ne hle hlabelNe
    have hzReach : θ.IncreasingReach b z :=
      Relation.ReflTransGen.tail hsinkReach ⟨hout, hsinkz⟩
    have hzMem : z ∈ reachable := by simpa [reachable] using hzReach
    have hzle := hsinkMax z hzMem
    linarith
  · exact θ.weight_nonneg sink z

/-- The symmetric source statement, obtained by following predecessors. -/
theorem exists_occupied_source (θ : CouplingTable) (hscore : θ.score = betaPV)
    {a b : θ.Label} (hab : 0 < θ.weight a b)
    (hlt : θ.label a < θ.label b) :
    ∃ source next,
      θ.DecreasingPredecessorReach a source ∧
      0 < θ.weight source next ∧ θ.label source < θ.label next ∧
      ∀ z, z ≠ source → θ.weight z source = 0 := by
  classical
  let reachable : Finset θ.Label :=
    Finset.univ.filter (fun x => θ.DecreasingPredecessorReach a x)
  have hnonempty : reachable.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨source, hsourceMem, hsourceMin⟩ :=
    Finset.exists_min_image reachable θ.label hnonempty
  have hsourceReach : θ.DecreasingPredecessorReach a source := by
    simpa [reachable] using hsourceMem
  have houtgoing : ∃ next,
      0 < θ.weight source next ∧ θ.label source < θ.label next := by
    rcases Relation.ReflTransGen.cases_tail hsourceReach with heq | htail
    · subst source
      exact ⟨b, hab, hlt⟩
    · obtain ⟨current, _, hstep⟩ := htail
      exact ⟨current, hstep.1, hstep.2⟩
  obtain ⟨next, hnextWeight, hnextLt⟩ := houtgoing
  refine ⟨source, next, hsourceReach, hnextWeight, hnextLt, ?_⟩
  intro z hzsource
  apply le_antisymm
  · by_contra hnot
    have hin : 0 < θ.weight z source := lt_of_not_ge hnot
    have hzle : θ.label z ≤ θ.label source := by
      by_contra hnotle
      have hsourcez : θ.label source < θ.label z := lt_of_not_ge hnotle
      have hcross : θ.label next ≤ θ.label source :=
        θ.occupied_ordered hscore hnextWeight hin hsourcez
      linarith
    have hlabelNe : θ.label z ≠ θ.label source := by
      intro heq
      exact hzsource (θ.label_injective heq)
    have hzlt : θ.label z < θ.label source := lt_of_le_of_ne hzle hlabelNe
    have hzReach : θ.DecreasingPredecessorReach a z :=
      Relation.ReflTransGen.tail hsourceReach ⟨hin, hzlt⟩
    have hzMem : z ∈ reachable := by simpa [reachable] using hzReach
    have hsourcele := hsourceMin z hzMem
    linarith
  · exact θ.weight_nonneg z source

/-- Sink extraction for a decreasing initial edge. -/
theorem exists_occupied_sink_of_decreasing (θ : CouplingTable)
    (hscore : θ.score = betaPV) {a b : θ.Label}
    (hab : 0 < θ.weight a b) (hlt : θ.label b < θ.label a) :
    ∃ sink pred,
      θ.DecreasingReach b sink ∧
      0 < θ.weight pred sink ∧ θ.label sink < θ.label pred ∧
      ∀ z, z ≠ sink → θ.weight sink z = 0 := by
  classical
  let reachable : Finset θ.Label :=
    Finset.univ.filter (fun x => θ.DecreasingReach b x)
  have hnonempty : reachable.Nonempty := by
    refine ⟨b, ?_⟩
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨sink, hsinkMem, hsinkMin⟩ :=
    Finset.exists_min_image reachable θ.label hnonempty
  have hsinkReach : θ.DecreasingReach b sink := by
    simpa [reachable] using hsinkMem
  have hincoming : ∃ pred,
      0 < θ.weight pred sink ∧ θ.label sink < θ.label pred := by
    rcases Relation.ReflTransGen.cases_tail hsinkReach with heq | htail
    · subst sink
      exact ⟨a, hab, hlt⟩
    · obtain ⟨pred, _, hpred⟩ := htail
      exact ⟨pred, hpred.1, hpred.2⟩
  obtain ⟨pred, hpredWeight, hpredLt⟩ := hincoming
  refine ⟨sink, pred, hsinkReach, hpredWeight, hpredLt, ?_⟩
  intro z hzsink
  apply le_antisymm
  · by_contra hnot
    have hout : 0 < θ.weight sink z := lt_of_not_ge hnot
    have hzle : θ.label z ≤ θ.label sink := by
      exact θ.occupied_ordered hscore hout hpredWeight hpredLt
    have hlabelNe : θ.label z ≠ θ.label sink := by
      intro heq
      exact hzsink (θ.label_injective heq)
    have hzlt : θ.label z < θ.label sink := lt_of_le_of_ne hzle hlabelNe
    have hzReach : θ.DecreasingReach b z :=
      Relation.ReflTransGen.tail hsinkReach ⟨hout, hzlt⟩
    have hzMem : z ∈ reachable := by simpa [reachable] using hzReach
    have hsinkle := hsinkMin z hzMem
    linarith
  · exact θ.weight_nonneg sink z

/-- Source extraction for a decreasing initial edge. -/
theorem exists_occupied_source_of_decreasing (θ : CouplingTable)
    (hscore : θ.score = betaPV) {a b : θ.Label}
    (hab : 0 < θ.weight a b) (hlt : θ.label b < θ.label a) :
    ∃ source next,
      θ.IncreasingPredecessorReach a source ∧
      0 < θ.weight source next ∧ θ.label next < θ.label source ∧
      ∀ z, z ≠ source → θ.weight z source = 0 := by
  classical
  let reachable : Finset θ.Label :=
    Finset.univ.filter (fun x => θ.IncreasingPredecessorReach a x)
  have hnonempty : reachable.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨source, hsourceMem, hsourceMax⟩ :=
    Finset.exists_max_image reachable θ.label hnonempty
  have hsourceReach : θ.IncreasingPredecessorReach a source := by
    simpa [reachable] using hsourceMem
  have houtgoing : ∃ next,
      0 < θ.weight source next ∧ θ.label next < θ.label source := by
    rcases Relation.ReflTransGen.cases_tail hsourceReach with heq | htail
    · subst source
      exact ⟨b, hab, hlt⟩
    · obtain ⟨current, _, hstep⟩ := htail
      exact ⟨current, hstep.1, hstep.2⟩
  obtain ⟨next, hnextWeight, hnextLt⟩ := houtgoing
  refine ⟨source, next, hsourceReach, hnextWeight, hnextLt, ?_⟩
  intro z hzsource
  apply le_antisymm
  · by_contra hnot
    have hin : 0 < θ.weight z source := lt_of_not_ge hnot
    have hsourcele : θ.label source ≤ θ.label z := by
      by_contra hnotle
      have hzsourceLt : θ.label z < θ.label source := lt_of_not_ge hnotle
      have hcross : θ.label source ≤ θ.label next :=
        θ.occupied_ordered hscore hin hnextWeight hzsourceLt
      linarith
    have hlabelNe : θ.label source ≠ θ.label z := by
      intro heq
      exact hzsource (θ.label_injective heq).symm
    have hsourcelt : θ.label source < θ.label z :=
      lt_of_le_of_ne hsourcele hlabelNe
    have hzReach : θ.IncreasingPredecessorReach a z :=
      Relation.ReflTransGen.tail hsourceReach ⟨hin, hsourcelt⟩
    have hzMem : z ∈ reachable := by simpa [reachable] using hzReach
    have hzle := hsourceMax z hzMem
    linarith
  · exact θ.weight_nonneg z source

theorem row_eq_loop_of_no_offdiag_out (θ : CouplingTable) (c : θ.Label)
    (hout : ∀ z, z ≠ c → θ.weight c z = 0) :
    θ.row c = θ.weight c c := by
  classical
  unfold row
  rw [Finset.sum_eq_single c]
  · intro z _ hzc
    exact hout z hzc
  · simp

theorem column_eq_loop_of_no_offdiag_in (θ : CouplingTable) (c : θ.Label)
    (hin : ∀ z, z ≠ c → θ.weight z c = 0) :
    θ.column c = θ.weight c c := by
  classical
  unfold column
  rw [Finset.sum_eq_single c]
  · intro z _ hzc
    exact hin z hzc
  · simp

/-- At an extracted sink, the incoming marginal strictly exceeds the outgoing
marginal. -/
theorem sink_row_lt_column (θ : CouplingTable) {sink pred : θ.Label}
    (hpred : 0 < θ.weight pred sink) (hpredLt : θ.label pred < θ.label sink)
    (hout : ∀ z, z ≠ sink → θ.weight sink z = 0) :
    θ.row sink < θ.column sink := by
  classical
  have hpredNe : pred ≠ sink := by
    intro h
    subst pred
    linarith
  have hrow : θ.row sink = θ.weight sink sink :=
    θ.row_eq_loop_of_no_offdiag_out sink hout
  have hsinkMem : sink ∈ (Finset.univ.erase pred : Finset θ.Label) := by
    simp [Ne.symm hpredNe]
  have hrest : θ.weight sink sink ≤
      ∑ z ∈ (Finset.univ.erase pred : Finset θ.Label), θ.weight z sink := by
    exact Finset.single_le_sum (fun z _ => θ.weight_nonneg z sink) hsinkMem
  have hcolumn : θ.column sink = θ.weight pred sink +
      ∑ z ∈ (Finset.univ.erase pred : Finset θ.Label), θ.weight z sink := by
    unfold column
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pred)]
    ring
  rw [hrow, hcolumn]
  linarith

/-- At an extracted source, the outgoing marginal strictly exceeds the
incoming marginal. -/
theorem source_column_lt_row (θ : CouplingTable) {source next : θ.Label}
    (hnext : 0 < θ.weight source next) (hnextLt : θ.label source < θ.label next)
    (hin : ∀ z, z ≠ source → θ.weight z source = 0) :
    θ.column source < θ.row source := by
  classical
  have hnextNe : next ≠ source := by
    intro h
    subst next
    linarith
  have hcolumn : θ.column source = θ.weight source source :=
    θ.column_eq_loop_of_no_offdiag_in source hin
  have hsourceMem : source ∈ (Finset.univ.erase next : Finset θ.Label) := by
    simp [Ne.symm hnextNe]
  have hrest : θ.weight source source ≤
      ∑ z ∈ (Finset.univ.erase next : Finset θ.Label), θ.weight source z := by
    exact Finset.single_le_sum (fun z _ => θ.weight_nonneg source z) hsourceMem
  have hrow : θ.row source = θ.weight source next +
      ∑ z ∈ (Finset.univ.erase next : Finset θ.Label), θ.weight source z := by
    unfold row
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ next)]
    ring
  rw [hcolumn, hrow]
  linarith

/-- Pulling a common nonnegative scalar out of both factors under a square
root.  This is the elementary identity which makes all junctions away from a
spiked label scale exactly linearly. -/
theorem sqrt_scaled_product (q x y : ℝ) (hq : 0 ≤ q) :
    Real.sqrt ((q * x) * (q * y)) = q * Real.sqrt (x * y) := by
  rw [show (q * x) * (q * y) = q ^ 2 * (x * y) by ring]
  rw [Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq hq]

/-- Exact score formula for adding a loop at a label whose column marginal
vanishes. -/
theorem spikeScore_self_of_column_zero (θ : CouplingTable) (c : θ.Label)
    (hC : θ.column c = 0) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    θ.spikeScore c c t =
      (1 - t) * θ.score + t * d (θ.label c) (θ.label c) +
        s (θ.label c) * Real.sqrt (((1 - t) * θ.row c + t) * t) := by
  classical
  let base : θ.Label → ℝ := fun k =>
    s (θ.label k) * Real.sqrt (θ.row k * θ.column k)
  let pert : θ.Label → ℝ := fun k =>
    s (θ.label k) * Real.sqrt
      (((1 - t) * θ.row k + t * θ.point c k) *
        ((1 - t) * θ.column k + t * θ.point c k))
  have haway (k : θ.Label) (hk : k ≠ c) :
      pert k = (1 - t) * base k := by
    have hp : θ.point c k = 0 := θ.point_of_ne hk
    dsimp [pert, base]
    simp only [hp, mul_zero, add_zero]
    rw [sqrt_scaled_product (1 - t) _ _ (sub_nonneg.mpr ht1)]
    ring
  have hcbase : base c = 0 := by
    dsimp [base]
    rw [hC, mul_zero, Real.sqrt_zero, mul_zero]
  have hcpert : pert c =
      s (θ.label c) * Real.sqrt (((1 - t) * θ.row c + t) * t) := by
    dsimp [pert]
    simp [point_self, hC]
  have hsum : (∑ k, pert k) =
      (1 - t) * θ.junctionPart +
        s (θ.label c) * Real.sqrt (((1 - t) * θ.row c + t) * t) := by
    rw [← Finset.sum_erase_add Finset.univ pert (Finset.mem_univ c)]
    rw [Finset.sum_congr rfl (fun k hk => haway k (Finset.ne_of_mem_erase hk))]
    rw [← Finset.mul_sum, hcpert]
    unfold junctionPart
    change (1 - t) * (∑ k ∈ Finset.univ.erase c, base k) + _ = _
    rw [← Finset.sum_erase_add Finset.univ base (Finset.mem_univ c), hcbase]
    ring
  unfold spikeScore
  change (1 - t) * θ.diagonalPart + t * d (θ.label c) (θ.label c) +
      (∑ k, pert k) = _
  rw [hsum, score_eq_parts]
  ring

/-- Row/column-dual exact formula for a loop spike at a label whose row
marginal vanishes. -/
theorem spikeScore_self_of_row_zero (θ : CouplingTable) (c : θ.Label)
    (hR : θ.row c = 0) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    θ.spikeScore c c t =
      (1 - t) * θ.score + t * d (θ.label c) (θ.label c) +
        s (θ.label c) * Real.sqrt (t * ((1 - t) * θ.column c + t)) := by
  classical
  let base : θ.Label → ℝ := fun k =>
    s (θ.label k) * Real.sqrt (θ.row k * θ.column k)
  let pert : θ.Label → ℝ := fun k =>
    s (θ.label k) * Real.sqrt
      (((1 - t) * θ.row k + t * θ.point c k) *
        ((1 - t) * θ.column k + t * θ.point c k))
  have haway (k : θ.Label) (hk : k ≠ c) :
      pert k = (1 - t) * base k := by
    have hp : θ.point c k = 0 := θ.point_of_ne hk
    dsimp [pert, base]
    simp only [hp, mul_zero, add_zero]
    rw [sqrt_scaled_product (1 - t) _ _ (sub_nonneg.mpr ht1)]
    ring
  have hcbase : base c = 0 := by
    dsimp [base]
    rw [hR, zero_mul, Real.sqrt_zero, mul_zero]
  have hcpert : pert c =
      s (θ.label c) * Real.sqrt (t * ((1 - t) * θ.column c + t)) := by
    dsimp [pert]
    simp [point_self, hR]
  have hsum : (∑ k, pert k) =
      (1 - t) * θ.junctionPart +
        s (θ.label c) * Real.sqrt (t * ((1 - t) * θ.column c + t)) := by
    rw [← Finset.sum_erase_add Finset.univ pert (Finset.mem_univ c)]
    rw [Finset.sum_congr rfl (fun k hk => haway k (Finset.ne_of_mem_erase hk))]
    rw [← Finset.mul_sum, hcpert]
    unfold junctionPart
    change (1 - t) * (∑ k ∈ Finset.univ.erase c, base k) + _ = _
    rw [← Finset.sum_erase_add Finset.univ base (Finset.mem_univ c), hcbase]
    ring
  unfold spikeScore
  change (1 - t) * θ.diagonalPart + t * d (θ.label c) (θ.label c) +
      (∑ k, pert k) = _
  rw [hsum, score_eq_parts]
  ring

/-- First-label moment of a row, i.e. the derivative of its diagonal term
when that row label moves. -/
noncomputable def rowMoment (θ : CouplingTable) (c : θ.Label) : ℝ :=
  ∑ b, (θ.label b + 1 / 2) * θ.weight c b

/-- Second-label moment of a column. -/
noncomputable def columnMoment (θ : CouplingTable) (c : θ.Label) : ℝ :=
  ∑ a, (θ.label a - 1 / 2) * θ.weight a c

/-- Exact score change when moving a label with zero incoming marginal. -/
theorem relabelAt_score_of_column_zero (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hfresh : ∀ k, k ≠ c → x ≠ θ.label k)
    (hC : θ.column c = 0) :
    (θ.relabelAt c x hx hfresh).score =
      θ.score + (x - θ.label c) * θ.rowMoment c := by
  classical
  let ρ := θ.relabelAt c x hx hfresh
  have hzero : ∀ a, θ.weight a c = 0 := (θ.column_eq_zero_iff c).mp hC
  have hcell (a b : θ.Label) :
      d (ρ.label a) (ρ.label b) * ρ.weight a b =
        d (θ.label a) (θ.label b) * θ.weight a b +
          (if a = c then
            (x - θ.label c) * (θ.label b + 1 / 2) * θ.weight a b
          else 0) := by
    by_cases hb : b = c
    · subst b
      have hρzero : ρ.weight a c = 0 := by simpa [ρ] using hzero a
      rw [hzero a, hρzero]
      simp
    · by_cases ha : a = c
      · subst a
        simp [ρ, relabelAt, hb, d]
        ring
      · simp [ρ, relabelAt, ha, hb]
  have hdiag :
      (∑ a, ∑ b, d (ρ.label a) (ρ.label b) * ρ.weight a b) =
        (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
          (x - θ.label c) * θ.rowMoment c := by
    have hfactor :
        (∑ b, (x - θ.label c) * (θ.label b + 1 / 2) * θ.weight c b) =
          (x - θ.label c) * θ.rowMoment c := by
      unfold rowMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    calc
      (∑ a, ∑ b, d (ρ.label a) (ρ.label b) * ρ.weight a b) =
          ∑ a, ∑ b,
            (d (θ.label a) (θ.label b) * θ.weight a b +
              if a = c then
                (x - θ.label c) * (θ.label b + 1 / 2) * θ.weight a b
              else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hcell a b
      _ = (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
          (x - θ.label c) * θ.rowMoment c := by
        simp_rw [Finset.sum_add_distrib]
        simpa using hfactor
  have hjunction :
      (∑ k, s (ρ.label k) * Real.sqrt (ρ.row k * ρ.column k)) =
        ∑ k, s (θ.label k) * Real.sqrt (θ.row k * θ.column k) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = c
    · subst k
      rw [relabelAt_label_self, relabelAt_row, relabelAt_column, hC]
      simp
    · rw [relabelAt_label_of_ne θ c k x hx hfresh hk]
      rw [relabelAt_row, relabelAt_column]
  unfold score
  rw [hdiag, hjunction]
  ring

/-- Exact row/column-dual score change when moving a label with zero outgoing
marginal. -/
theorem relabelAt_score_of_row_zero (θ : CouplingTable) (c : θ.Label)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hfresh : ∀ k, k ≠ c → x ≠ θ.label k)
    (hR : θ.row c = 0) :
    (θ.relabelAt c x hx hfresh).score =
      θ.score + (x - θ.label c) * θ.columnMoment c := by
  classical
  let ρ := θ.relabelAt c x hx hfresh
  have hzero : ∀ b, θ.weight c b = 0 := (θ.row_eq_zero_iff c).mp hR
  have hcell (a b : θ.Label) :
      d (ρ.label a) (ρ.label b) * ρ.weight a b =
        d (θ.label a) (θ.label b) * θ.weight a b +
          (if b = c then
            (x - θ.label c) * (θ.label a - 1 / 2) * θ.weight a b
          else 0) := by
    by_cases ha : a = c
    · subst a
      have hρzero : ρ.weight c b = 0 := by simpa [ρ] using hzero b
      rw [hzero b, hρzero]
      simp
    · by_cases hb : b = c
      · subst b
        simp [ρ, relabelAt, ha, d]
        ring
      · simp [ρ, relabelAt, ha, hb]
  have hdiag :
      (∑ a, ∑ b, d (ρ.label a) (ρ.label b) * ρ.weight a b) =
        (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
          (x - θ.label c) * θ.columnMoment c := by
    have hfactor :
        (∑ a, (x - θ.label c) * (θ.label a - 1 / 2) * θ.weight a c) =
          (x - θ.label c) * θ.columnMoment c := by
      unfold columnMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    calc
      (∑ a, ∑ b, d (ρ.label a) (ρ.label b) * ρ.weight a b) =
          ∑ a, ∑ b,
            (d (θ.label a) (θ.label b) * θ.weight a b +
              if b = c then
                (x - θ.label c) * (θ.label a - 1 / 2) * θ.weight a b
              else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hcell a b
      _ = (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) +
          (x - θ.label c) * θ.columnMoment c := by
        simp_rw [Finset.sum_add_distrib]
        simpa using hfactor
  have hjunction :
      (∑ k, s (ρ.label k) * Real.sqrt (ρ.row k * ρ.column k)) =
        ∑ k, s (θ.label k) * Real.sqrt (θ.row k * θ.column k) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = c
    · subst k
      rw [relabelAt_label_self, relabelAt_row, relabelAt_column, hR]
      simp
    · rw [relabelAt_label_of_ne θ c k x hx hfresh hk]
      rw [relabelAt_row, relabelAt_column]
  unfold score
  rw [hdiag, hjunction]
  ring

/-- A finite injective label set has a punctured neighbourhood of any one of
its labels which contains no other label. -/
theorem exists_fresh_radius (θ : CouplingTable) (c : θ.Label) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : ℝ, |x - θ.label c| < ε →
        ∀ k, k ≠ c → x ≠ θ.label k := by
  classical
  let S : Finset θ.Label := Finset.univ.erase c
  by_cases hS : S.Nonempty
  · obtain ⟨k, hkS, hkmin⟩ :=
      Finset.exists_min_image S (fun j => |θ.label c - θ.label j|) hS
    have hkc : k ≠ c := Finset.ne_of_mem_erase hkS
    have hdistPos : 0 < |θ.label c - θ.label k| := abs_pos.mpr (by
      intro heq
      have hlab : θ.label c = θ.label k := sub_eq_zero.mp heq
      exact hkc (θ.label_injective hlab).symm)
    refine ⟨|θ.label c - θ.label k|, hdistPos, ?_⟩
    intro x hx j hj hxeq
    have hjS : j ∈ S := by simp [S, hj]
    have hmin := hkmin j hjS
    have hlt : |θ.label c - θ.label j| < |θ.label c - θ.label k| := by
      rw [← hxeq]
      simpa [abs_sub_comm] using hx
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro x _ k hk _
    have hkS : k ∈ S := by simp [S, hk]
    exact hS ⟨k, hkS⟩

theorem rowMoment_le (θ : CouplingTable) (c : θ.Label) :
    θ.rowMoment c ≤ (3 / 2 : ℝ) * θ.row c := by
  unfold rowMoment row
  calc
    (∑ b, (θ.label b + 1 / 2) * θ.weight c b) ≤
        ∑ b, (3 / 2 : ℝ) * θ.weight c b := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_right _ (θ.weight_nonneg c b)
      linarith [((θ.label_mem b).2)]
    _ = (3 / 2 : ℝ) * ∑ b, θ.weight c b := by rw [Finset.mul_sum]

theorem neg_half_mul_row_le_rowMoment (θ : CouplingTable) (c : θ.Label) :
    (-1 / 2 : ℝ) * θ.row c ≤ θ.rowMoment c := by
  unfold rowMoment row
  calc
    (-1 / 2 : ℝ) * (∑ b, θ.weight c b) =
        ∑ b, (-1 / 2 : ℝ) * θ.weight c b := Finset.mul_sum _ _ _
    _ ≤ ∑ b, (θ.label b + 1 / 2) * θ.weight c b := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_right _ (θ.weight_nonneg c b)
      linarith [((θ.label_mem b).1)]

theorem columnMoment_le (θ : CouplingTable) (c : θ.Label) :
    θ.columnMoment c ≤ (1 / 2 : ℝ) * θ.column c := by
  unfold columnMoment column
  calc
    (∑ a, (θ.label a - 1 / 2) * θ.weight a c) ≤
        ∑ a, (1 / 2 : ℝ) * θ.weight a c := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right _ (θ.weight_nonneg a c)
      linarith [((θ.label_mem a).2)]
    _ = (1 / 2 : ℝ) * ∑ a, θ.weight a c := by rw [Finset.mul_sum]

theorem neg_three_halves_mul_column_le_columnMoment
    (θ : CouplingTable) (c : θ.Label) :
    (-3 / 2 : ℝ) * θ.column c ≤ θ.columnMoment c := by
  unfold columnMoment column
  calc
    (-3 / 2 : ℝ) * (∑ a, θ.weight a c) =
        ∑ a, (-3 / 2 : ℝ) * θ.weight a c := Finset.mul_sum _ _ _
    _ ≤ ∑ a, (θ.label a - 1 / 2) * θ.weight a c := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right _ (θ.weight_nonneg a c)
      linarith [((θ.label_mem a).1)]

/-- Exact smooth expression obtained after moving a singular endpoint
`σ = ±1` to `σ(1-δ)` and adding loop mass `α²δ`. -/
noncomputable def boundarySpikeCurve (θ : CouplingTable) (c : θ.Label)
    (M A σ α δ : ℝ) : ℝ :=
  (1 - α ^ 2 * δ) * (θ.score - σ * δ * A) +
    α ^ 2 * δ * d (σ * (1 - δ)) (σ * (1 - δ)) +
    α * δ * Real.sqrt
      ((2 - δ) * ((1 - α ^ 2 * δ) * M + α ^ 2 * δ))

theorem boundarySpikeCurve_zero (θ : CouplingTable) (c : θ.Label)
    (M A σ α : ℝ) :
    θ.boundarySpikeCurve c M A σ α 0 = θ.score := by
  simp [boundarySpikeCurve]

theorem hasDerivAt_boundarySpikeCurve (θ : CouplingTable) (c : θ.Label)
    {M A σ α : ℝ} (hM : 0 < M) (hσ : σ ^ 2 = 1) :
    HasDerivAt (θ.boundarySpikeCurve c M A σ α)
      (-α ^ 2 * θ.score - σ * A + α * Real.sqrt (2 * M)) 0 := by
  have hid : HasDerivAt (fun δ : ℝ => δ) 1 0 := hasDerivAt_id 0
  have hscale : HasDerivAt (fun δ : ℝ => α ^ 2 * δ) (α ^ 2) 0 := by
    convert hid.mul_const (α ^ 2) using 1 <;> (try rfl) <;> ring
  have hone : HasDerivAt (fun δ : ℝ => 1 - α ^ 2 * δ) (-α ^ 2) 0 := by
    convert hscale.const_sub (1 : ℝ) using 1 <;> (try rfl) <;> ring
  have hscoreLine : HasDerivAt
      (fun δ : ℝ => θ.score - σ * δ * A) (-σ * A) 0 := by
    have hprod : HasDerivAt (fun δ : ℝ => σ * δ * A) (σ * A) 0 := by
      convert (hid.const_mul σ).mul_const A using 1 <;> (try rfl) <;> ring
    convert hprod.const_sub θ.score using 1 <;> (try rfl) <;> ring
  have hfirst : HasDerivAt
      (fun δ : ℝ => (1 - α ^ 2 * δ) * (θ.score - σ * δ * A))
      (-α ^ 2 * θ.score - σ * A) 0 := by
    convert hone.mul hscoreLine using 1 <;> (try rfl) <;> ring
  have hx : HasDerivAt (fun δ : ℝ => σ * (1 - δ)) (-σ) 0 := by
    convert (hid.const_sub (1 : ℝ)).const_mul σ using 1 <;> (try rfl) <;> ring
  have hd : HasDerivAt
      (fun δ : ℝ => d (σ * (1 - δ)) (σ * (1 - δ)))
      (-2 * σ ^ 2) 0 := by
    have heq :
        (fun δ : ℝ => d (σ * (1 - δ)) (σ * (1 - δ))) =
          fun δ : ℝ => (σ * (1 - δ)) * (σ * (1 - δ)) - 1 := by
      funext δ
      unfold d
      ring
    rw [heq]
    convert (hx.mul hx).sub_const 1 using 1
    all_goals try rfl
    all_goals try ring
    all_goals
      funext δ
      simp only [Pi.mul_apply]
      ring
  have hsecond : HasDerivAt
      (fun δ : ℝ => α ^ 2 * δ *
        d (σ * (1 - δ)) (σ * (1 - δ))) 0 0 := by
    have h := hscale.mul hd
    apply h.congr_deriv
    have hdzero : d σ σ = 0 := by
      unfold d
      nlinarith [hσ]
    norm_num [hdzero]
  have htwo : HasDerivAt (fun δ : ℝ => 2 - δ) (-1) 0 := by
    convert hid.const_sub (2 : ℝ) using 1 <;> (try rfl) <;> ring
  have hinsideRight : HasDerivAt
      (fun δ : ℝ => (1 - α ^ 2 * δ) * M + α ^ 2 * δ)
      (-α ^ 2 * M + α ^ 2) 0 := by
    convert (hone.mul_const M).add hscale using 1 <;> (try rfl) <;> ring
  have hinside : HasDerivAt
      (fun δ : ℝ =>
        (2 - δ) * ((1 - α ^ 2 * δ) * M + α ^ 2 * δ))
      (-M + 2 * (-α ^ 2 * M + α ^ 2)) 0 := by
    convert htwo.mul hinsideRight using 1 <;> (try rfl) <;> ring
  have hins0 :
      (2 - (0 : ℝ)) * ((1 - α ^ 2 * 0) * M + α ^ 2 * 0) ≠ 0 := by
    simp [ne_of_gt hM]
  have hsqrt : HasDerivAt
      (fun δ : ℝ => Real.sqrt
        ((2 - δ) * ((1 - α ^ 2 * δ) * M + α ^ 2 * δ)))
      ((-M + 2 * (-α ^ 2 * M + α ^ 2)) /
        (2 * Real.sqrt (2 * M))) 0 := by
    convert hinside.sqrt hins0 using 1 <;> (try rfl) <;> ring
  have hthird : HasDerivAt
      (fun δ : ℝ => α * δ * Real.sqrt
        ((2 - δ) * ((1 - α ^ 2 * δ) * M + α ^ 2 * δ)))
      (α * Real.sqrt (2 * M)) 0 := by
    have h := (hid.const_mul α).mul hsqrt
    convert h using 1 <;> (try rfl) <;> ring
  unfold boundarySpikeCurve
  convert (hfirst.add hsecond).add hthird using 1 <;> (try rfl) <;> ring

/-- Exact square-root identity behind the singular endpoint expansion.  It
replaces the paper's `O(δ²)` notation by an equality. -/
theorem singular_junction_rewrite {M σ α δ : ℝ}
    (hM : 0 ≤ M) (hσ : σ ^ 2 = 1) (hα : 0 ≤ α)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht1 : α ^ 2 * δ ≤ 1) :
    s (σ * (1 - δ)) *
        Real.sqrt (((1 - α ^ 2 * δ) * M + α ^ 2 * δ) *
          (α ^ 2 * δ)) =
      α * δ * Real.sqrt
        ((2 - δ) * ((1 - α ^ 2 * δ) * M + α ^ 2 * δ)) := by
  let B : ℝ := (1 - α ^ 2 * δ) * M + α ^ 2 * δ
  have ht0 : 0 ≤ α ^ 2 * δ := mul_nonneg (sq_nonneg α) hδ0
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hM) ht0
  have hx : 0 ≤ 1 - (σ * (1 - δ)) ^ 2 := by
    nlinarith [sq_nonneg δ, hσ]
  have htwo : 0 ≤ 2 - δ := by linarith
  have hs_sq : s (σ * (1 - δ)) ^ 2 =
      1 - (σ * (1 - δ)) ^ 2 := by
    unfold s
    exact Real.sq_sqrt hx
  have hleftSqrt_sq : Real.sqrt (B * (α ^ 2 * δ)) ^ 2 =
      B * (α ^ 2 * δ) := Real.sq_sqrt (mul_nonneg hB ht0)
  have hrightSqrt_sq : Real.sqrt ((2 - δ) * B) ^ 2 =
      (2 - δ) * B := Real.sq_sqrt (mul_nonneg htwo hB)
  have heqSq :
      (s (σ * (1 - δ)) * Real.sqrt (B * (α ^ 2 * δ))) ^ 2 =
        (α * δ * Real.sqrt ((2 - δ) * B)) ^ 2 := by
    rw [mul_pow, hs_sq, mul_pow, mul_pow, hleftSqrt_sq, hrightSqrt_sq]
    rw [hσ]
    ring
  have hleft : 0 ≤
      s (σ * (1 - δ)) * Real.sqrt (B * (α ^ 2 * δ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ α * δ * Real.sqrt ((2 - δ) * B) :=
    mul_nonneg (mul_nonneg hα hδ0) (Real.sqrt_nonneg _)
  change s (σ * (1 - δ)) * Real.sqrt (B * (α ^ 2 * δ)) =
    α * δ * Real.sqrt ((2 - δ) * B)
  nlinarith

/-- Every admissible singular source perturbation is still bounded by
`betaPV`; the left-hand side is the exact smooth curve above. -/
theorem boundarySourceCurve_le_betaPV (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label)
    {σ α δ : ℝ} (hlabel : θ.label c = σ) (hσ : σ ^ 2 = 1)
    (hα : 0 ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht1 : α ^ 2 * δ ≤ 1) (hC : θ.column c = 0)
    (hfresh : ∀ k, k ≠ c → σ * (1 - δ) ≠ θ.label k) :
    θ.boundarySpikeCurve c (θ.row c) (θ.rowMoment c) σ α δ ≤ betaPV := by
  let x : ℝ := σ * (1 - δ)
  let t : ℝ := α ^ 2 * δ
  have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases sq_eq_one_iff.mp hσ with hσone | hσneg
    · subst σ
      dsimp [x]
      constructor <;> nlinarith
    · subst σ
      dsimp [x]
      constructor <;> nlinarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (sq_nonneg α) hδ0
  let ρ := θ.relabelAt c x hxmem (by simpa [x] using hfresh)
  have hρlabel : ρ.label c = x := by
    dsimp [ρ]
    exact θ.relabelAt_label_self c x hxmem _
  have hρC : ρ.column c = 0 := by simpa [ρ] using hC
  have hρrow : ρ.row c = θ.row c := by simp [ρ]
  have hrel : ρ.score =
      θ.score + (x - θ.label c) * θ.rowMoment c := by
    exact θ.relabelAt_score_of_column_zero c x hxmem
      (by simpa [x] using hfresh) hC
  have hxminus : x - θ.label c = -σ * δ := by
    dsimp [x]
    rw [hlabel]
    ring
  have hjunction :
      s (ρ.label c) *
          Real.sqrt (((1 - t) * ρ.row c + t) * t) =
        α * δ * Real.sqrt
          ((2 - δ) * ((1 - α ^ 2 * δ) * θ.row c + α ^ 2 * δ)) := by
    rw [hρlabel]
    rw [hρrow]
    simpa [x, t] using singular_junction_rewrite
      (θ.row_nonneg c) hσ hα hδ0 hδ1 ht1
  have hformula := ρ.spikeScore_self_of_column_zero c hρC t ht0 ht1
  have hbound := Ensemble.score_le_betaPV (ρ.spike c c t ht0 ht1)
  rw [score_spike_eq_spikeScore] at hbound
  rw [hformula, hrel, hxminus, hjunction] at hbound
  rw [hρlabel] at hbound
  unfold boundarySpikeCurve
  rw [hscore]
  dsimp [x, t] at hbound
  rw [hscore] at hbound
  convert hbound using 1 <;> ring

/-- Row/column-dual singular sink perturbation bound. -/
theorem boundarySinkCurve_le_betaPV (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label)
    {σ α δ : ℝ} (hlabel : θ.label c = σ) (hσ : σ ^ 2 = 1)
    (hα : 0 ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht1 : α ^ 2 * δ ≤ 1) (hR : θ.row c = 0)
    (hfresh : ∀ k, k ≠ c → σ * (1 - δ) ≠ θ.label k) :
    θ.boundarySpikeCurve c (θ.column c) (θ.columnMoment c) σ α δ ≤ betaPV := by
  let x : ℝ := σ * (1 - δ)
  let t : ℝ := α ^ 2 * δ
  have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases sq_eq_one_iff.mp hσ with hσone | hσneg
    · subst σ
      dsimp [x]
      constructor <;> nlinarith
    · subst σ
      dsimp [x]
      constructor <;> nlinarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (sq_nonneg α) hδ0
  let ρ := θ.relabelAt c x hxmem (by simpa [x] using hfresh)
  have hρlabel : ρ.label c = x := by
    dsimp [ρ]
    exact θ.relabelAt_label_self c x hxmem _
  have hρR : ρ.row c = 0 := by simpa [ρ] using hR
  have hρcolumn : ρ.column c = θ.column c := by simp [ρ]
  have hrel : ρ.score =
      θ.score + (x - θ.label c) * θ.columnMoment c := by
    exact θ.relabelAt_score_of_row_zero c x hxmem
      (by simpa [x] using hfresh) hR
  have hxminus : x - θ.label c = -σ * δ := by
    dsimp [x]
    rw [hlabel]
    ring
  have hjunction :
      s (ρ.label c) *
          Real.sqrt (t * ((1 - t) * ρ.column c + t)) =
        α * δ * Real.sqrt
          ((2 - δ) * ((1 - α ^ 2 * δ) * θ.column c + α ^ 2 * δ)) := by
    rw [hρlabel]
    rw [hρcolumn]
    rw [mul_comm t]
    simpa [x, t] using singular_junction_rewrite
      (θ.column_nonneg c) hσ hα hδ0 hδ1 ht1
  have hformula := ρ.spikeScore_self_of_row_zero c hρR t ht0 ht1
  have hbound := Ensemble.score_le_betaPV (ρ.spike c c t ht0 ht1)
  rw [score_spike_eq_spikeScore] at hbound
  rw [hformula, hrel, hxminus, hjunction] at hbound
  rw [hρlabel] at hbound
  unfold boundarySpikeCurve
  rw [hscore]
  dsimp [x, t] at hbound
  rw [hscore] at hbound
  convert hbound using 1 <;> ring

theorem boundary_distance {σ δ : ℝ} (hσ : σ ^ 2 = 1) (hδ : 0 ≤ δ) :
    |σ * (1 - δ) - σ| = δ := by
  rcases sq_eq_one_iff.mp hσ with rfl | hneg
  · simp [abs_of_nonneg hδ]
  · subst σ
    simp [abs_of_nonneg hδ]

theorem signed_rowMoment_le (θ : CouplingTable) (c : θ.Label) {σ : ℝ}
    (hσ : σ ^ 2 = 1) :
    σ * θ.rowMoment c ≤ (3 / 2 : ℝ) * θ.row c := by
  rcases sq_eq_one_iff.mp hσ with rfl | hneg
  · simpa using θ.rowMoment_le c
  · subst σ
    have h := θ.neg_half_mul_row_le_rowMoment c
    have hrow := θ.row_nonneg c
    linarith

theorem signed_columnMoment_le (θ : CouplingTable) (c : θ.Label) {σ : ℝ}
    (hσ : σ ^ 2 = 1) :
    σ * θ.columnMoment c ≤ (3 / 2 : ℝ) * θ.column c := by
  rcases sq_eq_one_iff.mp hσ with rfl | hneg
  · have h := θ.columnMoment_le c
    have hcolumn := θ.column_nonneg c
    linarith
  · subst σ
    have h := θ.neg_three_halves_mul_column_le_columnMoment c
    linarith

/-- Abstract form of the exceptional-endpoint argument.  The `hbound`
premise follows from a relabelled-and-spiked coupling table for every
sufficiently small `δ`. -/
theorem singularEndpoint_false (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label) {M A σ : ℝ}
    (hlabel : θ.label c = σ) (hσ : σ ^ 2 = 1) (hM : 0 < M)
    (hmoment : σ * A ≤ (3 / 2 : ℝ) * M)
    (hbound : ∀ (α δ : ℝ), 0 ≤ α → 0 ≤ δ → δ ≤ 1 →
      α ^ 2 * δ ≤ 1 →
      (∀ k, k ≠ c → σ * (1 - δ) ≠ θ.label k) →
      θ.boundarySpikeCurve c M A σ α δ ≤ betaPV) : False := by
  let q : ℝ := Real.sqrt (2 * M)
  let α : ℝ := (3 / 2 : ℝ) * q
  have hq : 0 < q := Real.sqrt_pos.2 (by positivity)
  have hqSq : q ^ 2 = 2 * M := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hαSq : α ^ 2 = (9 / 2 : ℝ) * M := by
    dsimp [α]
    nlinarith
  have hgap : 0 < ((1 / 3 : ℝ) - betaPV) * M :=
    mul_pos (sub_pos.mpr betaPV_lt_third) hM
  have hderivPos :
      0 < -α ^ 2 * θ.score - σ * A + α * Real.sqrt (2 * M) := by
    rw [hscore, hαSq]
    dsimp [α]
    have hqdef : q = Real.sqrt (2 * M) := rfl
    rw [← hqdef]
    nlinarith
  obtain ⟨ε, hε, hfreshRadius⟩ := θ.exists_fresh_radius c
  let η : ℝ := min (ε / 2) (1 / (α ^ 2 + 1))
  have hden : 0 < α ^ 2 + 1 := by nlinarith [sq_nonneg α]
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · linarith
    · exact one_div_pos.mpr hden
  have hηeps : η ≤ ε / 2 := by exact min_le_left _ _
  have hηinv : η ≤ 1 / (α ^ 2 + 1) := by exact min_le_right _ _
  have hinvOne : 1 / (α ^ 2 + 1) ≤ (1 : ℝ) := by
    exact (div_le_one hden).2 (by nlinarith [sq_nonneg α])
  have hηone : η ≤ 1 := le_trans hηinv hinvOne
  have hmax : IsMaxOn (θ.boundarySpikeCurve c M A σ α)
      (Set.Icc (0 : ℝ) η) 0 := by
    intro δ hδ
    have hδone : δ ≤ 1 := le_trans hδ.2 hηone
    have ht : α ^ 2 * δ ≤ 1 := by
      calc
        α ^ 2 * δ ≤ α ^ 2 * (1 / (α ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_left (le_trans hδ.2 hηinv) (sq_nonneg α)
        _ = α ^ 2 / (α ^ 2 + 1) := by ring
        _ ≤ 1 := (div_le_one hden).2 (by linarith)
    have hδeps : δ < ε := by
      have : δ ≤ ε / 2 := le_trans hδ.2 hηeps
      linarith
    have hfresh : ∀ k, k ≠ c → σ * (1 - δ) ≠ θ.label k := by
      apply hfreshRadius (σ * (1 - δ))
      rw [hlabel, boundary_distance hσ hδ.1]
      exact hδeps
    have hle := hbound α δ (le_of_lt hα) hδ.1 hδone ht hfresh
    rw [boundarySpikeCurve_zero, hscore]
    exact hle
  have htangent : η ∈ posTangentConeAt (Set.Icc (0 : ℝ) η) 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset
      (x := (0 : ℝ)) (y := η) (s := Set.Icc (0 : ℝ) η) (by
        rw [segment_eq_Icc (le_of_lt hη)])
    simpa using h
  have hderiv := θ.hasDerivAt_boundarySpikeCurve c
    (M := M) (A := A) (σ := σ) (α := α) hM hσ
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    (hasDerivWithinAt_iff_hasFDerivWithinAt.mp hderiv.hasDerivWithinAt)
    htangent
  have hproduct :
      (-α ^ 2 * θ.score - σ * A + α * Real.sqrt (2 * M)) * η ≤ 0 := by
    simpa [mul_comm] using hnonpos
  exact (not_le_of_gt (mul_pos hderivPos hη)) hproduct

/-- The smooth reparametrization `t = u^2` of a loop spike.  The parameter
`M` is the nonzero marginal at the endpoint. -/
noncomputable def loopSpikeCurve (θ : CouplingTable) (c : θ.Label)
    (M : ℝ) (u : ℝ) : ℝ :=
  (1 - u ^ 2) * θ.score + u ^ 2 * d (θ.label c) (θ.label c) +
    s (θ.label c) * u * Real.sqrt ((1 - u ^ 2) * M + u ^ 2)

theorem hasDerivAt_loopSpikeCurve (θ : CouplingTable) (c : θ.Label)
    {M : ℝ} (hM : 0 < M) :
    HasDerivAt (θ.loopSpikeCurve c M)
      (s (θ.label c) * Real.sqrt M) 0 := by
  have hu2 : HasDerivAt (fun u : ℝ => u ^ 2) 0 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).pow 2 using 1 <;>
      norm_num <;> rfl
  have hinside : HasDerivAt
      (fun u : ℝ => (1 - u ^ 2) * M + u ^ 2) 0 0 := by
    convert ((hu2.const_sub (1 : ℝ)).mul_const M).add hu2 using 1 <;>
      norm_num <;> rfl
  have hsqrt : HasDerivAt
      (fun u : ℝ => Real.sqrt ((1 - u ^ 2) * M + u ^ 2))
      0 0 := by
    have hM0 : (1 - (0 : ℝ) ^ 2) * M + (0 : ℝ) ^ 2 ≠ 0 := by
      simpa using hM.ne'
    simpa using hinside.sqrt hM0
  have hfirst : HasDerivAt
      (fun u : ℝ => (1 - u ^ 2) * θ.score) 0 0 := by
    convert (hu2.const_sub (1 : ℝ)).mul_const θ.score using 1 <;>
      norm_num <;> rfl
  have hsecond : HasDerivAt
      (fun u : ℝ => u ^ 2 * d (θ.label c) (θ.label c)) 0 0 := by
    convert hu2.mul_const (d (θ.label c) (θ.label c)) using 1 <;>
      norm_num <;> rfl
  have hjunction : HasDerivAt
      (fun u : ℝ => s (θ.label c) * u *
        Real.sqrt ((1 - u ^ 2) * M + u ^ 2))
      (s (θ.label c) * Real.sqrt M) 0 := by
    have hmul := (hasDerivAt_id (𝕜 := ℝ) 0).mul hsqrt
    have hconst := hmul.const_mul (s (θ.label c))
    simpa [mul_assoc] using hconst
  unfold loopSpikeCurve
  convert (hfirst.add hsecond).add hjunction using 1 <;>
    norm_num <;> rfl

theorem loopSpikeCurve_zero (θ : CouplingTable) (c : θ.Label) (M : ℝ) :
    θ.loopSpikeCurve c M 0 = θ.score := by
  simp [loopSpikeCurve]

/-- If the one nonzero endpoint marginal is positive and `s(c)>0`, the
quadratically parametrized loop spike has strictly positive right derivative,
so it cannot be maximal at zero. -/
theorem not_isMaxOn_loopSpikeCurve (θ : CouplingTable) (c : θ.Label)
    {M : ℝ} (hM : 0 < M) (hs : 0 < s (θ.label c)) :
    ¬ IsMaxOn (θ.loopSpikeCurve c M) (Set.Icc (0 : ℝ) 1) 0 := by
  intro hmax
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset
      (x := (0 : ℝ)) (y := (1 : ℝ))
      (s := Set.Icc (0 : ℝ) 1) (by
        rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)])
    simpa using h
  have hderiv := θ.hasDerivAt_loopSpikeCurve c hM
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    (hasDerivWithinAt_iff_hasFDerivWithinAt.mp hderiv.hasDerivWithinAt)
    htangent
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have : s (θ.label c) * Real.sqrt M ≤ 0 := by simpa using hnonpos
  exact (not_le_of_gt (mul_pos hs hsqrt)) this

/-- An equality table cannot have a positive row, zero column, and an
interior label. -/
theorem s_eq_zero_of_column_zero (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label)
    (hR : 0 < θ.row c) (hC : θ.column c = 0) :
    s (θ.label c) = 0 := by
  apply le_antisymm
  · by_contra hsnot
    have hs : 0 < s (θ.label c) := lt_of_not_ge hsnot
    apply θ.not_isMaxOn_loopSpikeCurve c hR hs
    intro u hu
    have hu2_nonneg : 0 ≤ u ^ 2 := sq_nonneg u
    have hu2_le : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hinside : 0 ≤ (1 - u ^ 2) * θ.row c + u ^ 2 :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hu2_le) (θ.row_nonneg c))
        hu2_nonneg
    have hsqrt : Real.sqrt
        (((1 - u ^ 2) * θ.row c + u ^ 2) * u ^ 2) =
        u * Real.sqrt ((1 - u ^ 2) * θ.row c + u ^ 2) := by
      rw [Real.sqrt_mul hinside, Real.sqrt_sq hu.1]
      ring
    have hformula := θ.spikeScore_self_of_column_zero c hC (u ^ 2)
      hu2_nonneg hu2_le
    rw [hsqrt] at hformula
    have hbound := Ensemble.score_le_betaPV
      (θ.spike c c (u ^ 2) hu2_nonneg hu2_le)
    rw [score_spike_eq_spikeScore] at hbound
    rw [hformula] at hbound
    change θ.loopSpikeCurve c (θ.row c) u ≤ θ.loopSpikeCurve c (θ.row c) 0
    rw [loopSpikeCurve_zero, hscore]
    simpa [loopSpikeCurve, mul_assoc] using hbound
  · exact Real.sqrt_nonneg _

/-- Row/column-dual endpoint statement. -/
theorem s_eq_zero_of_row_zero (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label)
    (hR : θ.row c = 0) (hC : 0 < θ.column c) :
    s (θ.label c) = 0 := by
  apply le_antisymm
  · by_contra hsnot
    have hs : 0 < s (θ.label c) := lt_of_not_ge hsnot
    apply θ.not_isMaxOn_loopSpikeCurve c hC hs
    intro u hu
    have hu2_nonneg : 0 ≤ u ^ 2 := sq_nonneg u
    have hu2_le : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hinside : 0 ≤ (1 - u ^ 2) * θ.column c + u ^ 2 :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hu2_le) (θ.column_nonneg c))
        hu2_nonneg
    have hsqrt : Real.sqrt
        (u ^ 2 * ((1 - u ^ 2) * θ.column c + u ^ 2)) =
        u * Real.sqrt ((1 - u ^ 2) * θ.column c + u ^ 2) := by
      rw [Real.sqrt_mul hu2_nonneg, Real.sqrt_sq hu.1]
    have hformula := θ.spikeScore_self_of_row_zero c hR (u ^ 2)
      hu2_nonneg hu2_le
    rw [hsqrt] at hformula
    have hbound := Ensemble.score_le_betaPV
      (θ.spike c c (u ^ 2) hu2_nonneg hu2_le)
    rw [score_spike_eq_spikeScore] at hbound
    rw [hformula] at hbound
    change θ.loopSpikeCurve c (θ.column c) u ≤
      θ.loopSpikeCurve c (θ.column c) 0
    rw [loopSpikeCurve_zero, hscore]
    simpa [loopSpikeCurve, mul_assoc] using hbound
  · exact Real.sqrt_nonneg _

/-- Equality forces every positive row to have a positive matching column. -/
theorem column_pos_of_row_pos_eq (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label) (hR : 0 < θ.row c) :
    0 < θ.column c := by
  by_contra hnpos
  have hC : θ.column c = 0 :=
    le_antisymm (le_of_not_gt hnpos) (θ.column_nonneg c)
  have hs := θ.s_eq_zero_of_column_zero hscore c hR hC
  have hinside : 0 ≤ 1 - θ.label c ^ 2 := by
    rcases θ.label_mem c with ⟨hcL, hcR⟩
    nlinarith
  have hσ : θ.label c ^ 2 = 1 := by
    have := (Real.sqrt_eq_zero hinside).mp hs
    linarith
  exact θ.singularEndpoint_false hscore c rfl hσ hR
    (θ.signed_rowMoment_le c hσ) (by
      intro α δ hα hδ0 hδ1 ht hfresh
      exact θ.boundarySourceCurve_le_betaPV hscore c rfl hσ hα hδ0 hδ1
        ht hC hfresh)

/-- Equality forces every positive column to have a positive matching row. -/
theorem row_pos_of_column_pos_eq (θ : CouplingTable)
    (hscore : θ.score = betaPV) (c : θ.Label) (hC : 0 < θ.column c) :
    0 < θ.row c := by
  by_contra hnpos
  have hR : θ.row c = 0 :=
    le_antisymm (le_of_not_gt hnpos) (θ.row_nonneg c)
  have hs := θ.s_eq_zero_of_row_zero hscore c hR hC
  have hinside : 0 ≤ 1 - θ.label c ^ 2 := by
    rcases θ.label_mem c with ⟨hcL, hcR⟩
    nlinarith
  have hσ : θ.label c ^ 2 = 1 := by
    have := (Real.sqrt_eq_zero hinside).mp hs
    linarith
  exact θ.singularEndpoint_false hscore c rfl hσ hC
    (θ.signed_columnMoment_le c hσ) (by
      intro α δ hα hδ0 hδ1 ht hfresh
      exact θ.boundarySinkCurve_le_betaPV hscore c rfl hσ hα hδ0 hδ1
        ht hR hfresh)

/-- A positive loop in an equality table cannot sit at either singular label
`-1` or `1`. -/
theorem loop_label_mem_Ioo (θ : CouplingTable) (hscore : θ.score = betaPV)
    (c : θ.Label) (hloop : 0 < θ.weight c c) :
    θ.label c ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases θ.label_mem c with ⟨hleft, hright⟩
  refine ⟨lt_of_le_of_ne hleft ?_, lt_of_le_of_ne hright ?_⟩
  · intro heq
    have htight := θ.occupied_tight hscore hloop
    have hc : θ.label c = -1 := heq.symm
    unfold gain leftSlope rightSlope at htight
    simp [hc, d, s] at htight
    linarith [quarter_lt_betaPV]
  · intro heq
    have htight := θ.occupied_tight hscore hloop
    have hc : θ.label c = 1 := heq
    unfold gain leftSlope rightSlope at htight
    simp [hc, d, s] at htight
    linarith [quarter_lt_betaPV]

/-- A table supported on its diagonal has score at most `1/4`. -/
theorem score_le_quarter_of_offdiag_zero (θ : CouplingTable)
    (hoff : ∀ a b, a ≠ b → θ.weight a b = 0) :
    θ.score ≤ (1 / 4 : ℝ) := by
  classical
  have hrow (c : θ.Label) : θ.row c = θ.weight c c := by
    unfold row
    rw [Finset.sum_eq_single c]
    · intro b _ hbc
      exact hoff c b (Ne.symm hbc)
    · simp
  have hcolumn (c : θ.Label) : θ.column c = θ.weight c c := by
    unfold column
    rw [Finset.sum_eq_single c]
    · intro a _ hac
      exact hoff a c hac
    · simp
  have hdiag :
      (∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b) =
        ∑ c, d (θ.label c) (θ.label c) * θ.weight c c := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single a]
    · intro b _ hba
      rw [hoff a b (Ne.symm hba), mul_zero]
    · simp
  rw [score, hdiag]
  simp_rw [hrow, hcolumn]
  have hsqrt (c : θ.Label) :
      Real.sqrt (θ.weight c c * θ.weight c c) = θ.weight c c := by
    rw [← sq]
    exact Real.sqrt_sq (θ.weight_nonneg c c)
  simp_rw [hsqrt]
  calc
    (∑ c, d (θ.label c) (θ.label c) * θ.weight c c) +
        ∑ c, s (θ.label c) * θ.weight c c =
        ∑ c, (d (θ.label c) (θ.label c) + s (θ.label c)) *
          θ.weight c c := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c, (1 / 4 : ℝ) * θ.weight c c := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_right _ (θ.weight_nonneg c c)
      unfold d s
      let x := Real.sqrt (1 - θ.label c ^ 2)
      have hx : 0 ≤ x := Real.sqrt_nonneg _
      have hsq : x ^ 2 = 1 - θ.label c ^ 2 := by
        dsimp [x]
        rw [Real.sq_sqrt]
        rcases θ.label_mem c with ⟨hcL, hcR⟩
        nlinarith
      nlinarith [sq_nonneg (x - 1 / 2)]
    _ = (1 / 4 : ℝ) := by
      rw [← Finset.mul_sum]
      have htotalDiag : ∑ c, θ.weight c c = 1 := by
        calc
          (∑ c, θ.weight c c) = ∑ a, ∑ b, θ.weight a b := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_eq_single a]
            · intro b _ hba
              exact hoff a b (Ne.symm hba)
            · simp
          _ = 1 := θ.totalWeight
      rw [htotalDiag]
      norm_num

/-- An equality table must contain an occupied non-diagonal cell. -/
theorem exists_offdiag_weight_pos_of_eq (θ : CouplingTable)
    (hscore : θ.score = betaPV) :
    ∃ a b, a ≠ b ∧ 0 < θ.weight a b := by
  by_contra h
  push Not at h
  have hoff : ∀ a b, a ≠ b → θ.weight a b = 0 := by
    intro a b hab
    exact le_antisymm (h a b hab) (θ.weight_nonneg a b)
  have hle := θ.score_le_quarter_of_offdiag_zero hoff
  rw [hscore] at hle
  exact (not_le_of_gt quarter_lt_betaPV) hle

/-- A finite, strictly monotone occupied path between an extracted source and
sink.  The endpoint maximality conditions say precisely that only a loop may
enter the source or leave the sink. -/
structure SupportSpine (θ : CouplingTable) where
  n : ℕ
  n_pos : 0 < n
  node : Fin (n + 1) → θ.Label
  edge_pos : ∀ j : Fin n, 0 < θ.weight (node j.castSucc) (node j.succ)
  ordered :
    (∀ j : Fin n, θ.label (node j.castSucc) < θ.label (node j.succ)) ∨
    (∀ j : Fin n, θ.label (node j.succ) < θ.label (node j.castSucc))
  source_no_offdiag_in :
    ∀ z, z ≠ node 0 → θ.weight z (node 0) = 0
  sink_no_offdiag_out :
    ∀ z, z ≠ node (Fin.last n) → θ.weight (node (Fin.last n)) z = 0

theorem increasingReach_label_le (θ : CouplingTable) {a b : θ.Label}
    (h : θ.IncreasingReach a b) : θ.label a ≤ θ.label b := by
  induction h with
  | refl => exact le_rfl
  | tail hxy hyz ih => exact le_trans ih (le_of_lt hyz.2)

theorem decreasingReach_label_ge (θ : CouplingTable) {a b : θ.Label}
    (h : θ.DecreasingReach a b) : θ.label b ≤ θ.label a := by
  induction h with
  | refl => exact le_rfl
  | tail hxy hyz ih => exact le_trans (le_of_lt hyz.2) ih

/-- The graph-theoretic extraction, packaged as a finite indexed spine. -/
theorem exists_supportSpine (θ : CouplingTable)
    (hscore : θ.score = betaPV) : Nonempty θ.SupportSpine := by
  classical
  obtain ⟨a, b, habNe, hab⟩ := θ.exists_offdiag_weight_pos_of_eq hscore
  have hlabelNe : θ.label a ≠ θ.label b := fun h => habNe (θ.label_injective h)
  rcases lt_or_gt_of_ne hlabelNe with hablt | habgt
  · obtain ⟨source, next, hsourceReach, hsourceNext, hsourceLt,
        hsourceNoIn⟩ := θ.exists_occupied_source hscore hab hablt
    obtain ⟨sink, pred, hsinkReach, hpredSink, hpredLt,
        hsinkNoOut⟩ := θ.exists_occupied_sink hscore hab hablt
    have hsourceToA : Relation.ReflTransGen θ.IncreasingEdge source a := by
      exact (Relation.ReflTransGen.mono
        (r := Function.swap θ.DecreasingPredecessorEdge)
        (p := θ.IncreasingEdge) (by
          intro x y hxy
          exact hxy)) source a hsourceReach.swap
    have hpath : Relation.ReflTransGen θ.IncreasingEdge source sink :=
      (hsourceToA.tail ⟨hab, hablt⟩).trans hsinkReach
    have hsourceLeA := θ.increasingReach_label_le hsourceToA
    have hBSink := θ.increasingReach_label_le hsinkReach
    have hsourceSink : θ.label source < θ.label sink := by linarith
    have hsourceNeSink : source ≠ sink := by
      intro h
      subst sink
      linarith
    obtain ⟨tail, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen hpath
    have htail : 0 < tail.length := by
      by_contra hnot
      have hzero : tail.length = 0 := Nat.eq_zero_of_not_pos hnot
      have hempty : tail = [] := List.eq_nil_of_length_eq_zero hzero
      subst tail
      simp at hlast
      exact hsourceNeSink hlast
    let node : Fin (tail.length + 1) → θ.Label := fun i =>
      (source :: tail)[i.1]'(by simpa using i.2)
    have hnodeZero : node 0 = source := by simp [node]
    have hnodeLast : node (Fin.last tail.length) = sink := by
      simpa [node, List.getLast_eq_getElem] using hlast
    refine ⟨{
      n := tail.length
      n_pos := htail
      node := node
      edge_pos := ?_
      ordered := Or.inl ?_
      source_no_offdiag_in := ?_
      sink_no_offdiag_out := ?_ }⟩
    · intro j
      have hj := hchain.getElem j.1 (by simpa using j.2)
      exact hj.1
    · intro j
      have hj := hchain.getElem j.1 (by simpa using j.2)
      exact hj.2
    · rw [hnodeZero]
      exact hsourceNoIn
    · rw [hnodeLast]
      exact hsinkNoOut
  · obtain ⟨source, next, hsourceReach, hsourceNext, hnextLt,
        hsourceNoIn⟩ := θ.exists_occupied_source_of_decreasing hscore hab habgt
    obtain ⟨sink, pred, hsinkReach, hpredSink, hsinkPredLt,
        hsinkNoOut⟩ := θ.exists_occupied_sink_of_decreasing hscore hab habgt
    have hsourceToA : Relation.ReflTransGen θ.DecreasingEdge source a := by
      exact (Relation.ReflTransGen.mono
        (r := Function.swap θ.IncreasingPredecessorEdge)
        (p := θ.DecreasingEdge) (by
          intro x y hxy
          exact hxy)) source a hsourceReach.swap
    have hpath : Relation.ReflTransGen θ.DecreasingEdge source sink :=
      (hsourceToA.tail ⟨hab, habgt⟩).trans hsinkReach
    have hsourceSink : θ.label sink < θ.label source := by
      have hsourceGeA := θ.decreasingReach_label_ge hsourceToA
      have hBSink := θ.decreasingReach_label_ge hsinkReach
      linarith
    have hsourceNeSink : source ≠ sink := by
      intro h
      subst sink
      linarith
    obtain ⟨tail, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen hpath
    have htail : 0 < tail.length := by
      by_contra hnot
      have hzero : tail.length = 0 := Nat.eq_zero_of_not_pos hnot
      have hempty : tail = [] := List.eq_nil_of_length_eq_zero hzero
      subst tail
      simp at hlast
      exact hsourceNeSink hlast
    let node : Fin (tail.length + 1) → θ.Label := fun i =>
      (source :: tail)[i.1]'(by simpa using i.2)
    have hnodeZero : node 0 = source := by simp [node]
    have hnodeLast : node (Fin.last tail.length) = sink := by
      simpa [node, List.getLast_eq_getElem] using hlast
    refine ⟨{
      n := tail.length
      n_pos := htail
      node := node
      edge_pos := ?_
      ordered := Or.inr ?_
      source_no_offdiag_in := ?_
      sink_no_offdiag_out := ?_ }⟩
    · intro j
      have hj := hchain.getElem j.1 (by simpa using j.2)
      exact hj.1
    · intro j
      have hj := hchain.getElem j.1 (by simpa using j.2)
      exact hj.2
    · rw [hnodeZero]
      exact hsourceNoIn
    · rw [hnodeLast]
      exact hsinkNoOut

namespace SupportSpine

noncomputable def ratio {θ : CouplingTable} (p : θ.SupportSpine)
    (j : Fin (p.n + 1)) : ℝ :=
  Real.sqrt (θ.row (p.node j) * θ.column (p.node j)) /
    θ.column (p.node j)

theorem first_edge_pos {θ : CouplingTable} (p : θ.SupportSpine) :
    0 < θ.weight (p.node 0)
      (p.node ⟨1, Nat.succ_lt_succ p.n_pos⟩) := by
  simpa using p.edge_pos ⟨0, p.n_pos⟩

theorem first_nodes_ne {θ : CouplingTable} (p : θ.SupportSpine) :
    p.node 0 ≠ p.node ⟨1, Nat.succ_lt_succ p.n_pos⟩ := by
  intro h
  have ho := p.ordered
  rcases ho with hinc | hdec
  · have := hinc ⟨0, p.n_pos⟩
    simpa [h] using this
  · have := hdec ⟨0, p.n_pos⟩
    simpa [h] using this

theorem source_column_lt_row {θ : CouplingTable} (p : θ.SupportSpine) :
    θ.column (p.node 0) < θ.row (p.node 0) := by
  classical
  let next : θ.Label := p.node ⟨1, Nat.succ_lt_succ p.n_pos⟩
  have hnext : 0 < θ.weight (p.node 0) next := p.first_edge_pos
  have hnextNe : next ≠ p.node 0 := (p.first_nodes_ne).symm
  have hcolumn : θ.column (p.node 0) = θ.weight (p.node 0) (p.node 0) :=
    θ.column_eq_loop_of_no_offdiag_in (p.node 0) p.source_no_offdiag_in
  have hmem : p.node 0 ∈ (Finset.univ.erase next : Finset θ.Label) := by
    simp [Ne.symm hnextNe]
  have hrest : θ.weight (p.node 0) (p.node 0) ≤
      ∑ z ∈ (Finset.univ.erase next : Finset θ.Label),
        θ.weight (p.node 0) z := by
    exact Finset.single_le_sum (fun z _ => θ.weight_nonneg (p.node 0) z) hmem
  have hrow : θ.row (p.node 0) = θ.weight (p.node 0) next +
      ∑ z ∈ (Finset.univ.erase next : Finset θ.Label),
        θ.weight (p.node 0) z := by
    unfold CouplingTable.row
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ next)]
    ring
  rw [hcolumn, hrow]
  linarith

theorem last_edge_pos {θ : CouplingTable} (p : θ.SupportSpine) :
    ∃ pred : θ.Label,
      pred ≠ p.node (Fin.last p.n) ∧
      0 < θ.weight pred (p.node (Fin.last p.n)) := by
  let j : Fin p.n := ⟨p.n - 1, Nat.sub_lt p.n_pos Nat.zero_lt_one⟩
  have hs : j.succ = Fin.last p.n := by
    ext
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt p.n_pos))
  refine ⟨p.node j.castSucc, ?_, ?_⟩
  · intro h
    rcases p.ordered with hinc | hdec
    · have ho := hinc j
      rw [hs, h] at ho
      exact (lt_irrefl _ ho)
    · have ho := hdec j
      rw [hs, h] at ho
      exact (lt_irrefl _ ho)
  · simpa [hs] using p.edge_pos j

theorem sink_row_lt_column {θ : CouplingTable} (p : θ.SupportSpine) :
    θ.row (p.node (Fin.last p.n)) < θ.column (p.node (Fin.last p.n)) := by
  classical
  obtain ⟨pred, hpredNe, hpred⟩ := p.last_edge_pos
  have hrow : θ.row (p.node (Fin.last p.n)) =
      θ.weight (p.node (Fin.last p.n)) (p.node (Fin.last p.n)) :=
    θ.row_eq_loop_of_no_offdiag_out _ p.sink_no_offdiag_out
  have hmem : p.node (Fin.last p.n) ∈
      (Finset.univ.erase pred : Finset θ.Label) := by simp [Ne.symm hpredNe]
  have hrest : θ.weight (p.node (Fin.last p.n)) (p.node (Fin.last p.n)) ≤
      ∑ z ∈ (Finset.univ.erase pred : Finset θ.Label),
        θ.weight z (p.node (Fin.last p.n)) := by
    exact Finset.single_le_sum (fun z _ => θ.weight_nonneg z _) hmem
  have hcolumn : θ.column (p.node (Fin.last p.n)) =
      θ.weight pred (p.node (Fin.last p.n)) +
      ∑ z ∈ (Finset.univ.erase pred : Finset θ.Label),
        θ.weight z (p.node (Fin.last p.n)) := by
    unfold CouplingTable.column
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pred)]
    ring
  rw [hrow, hcolumn]
  linarith

theorem source_loop_pos {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) : 0 < θ.weight (p.node 0) (p.node 0) := by
  have hR : 0 < θ.row (p.node 0) :=
    θ.row_pos_of_weight_pos p.first_edge_pos
  have hC := θ.column_pos_of_row_pos_eq hscore (p.node 0) hR
  rw [θ.column_eq_loop_of_no_offdiag_in _ p.source_no_offdiag_in] at hC
  exact hC

theorem sink_loop_pos {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) :
    0 < θ.weight (p.node (Fin.last p.n)) (p.node (Fin.last p.n)) := by
  obtain ⟨pred, _, hpred⟩ := p.last_edge_pos
  have hC : 0 < θ.column (p.node (Fin.last p.n)) :=
    θ.column_pos_of_weight_pos hpred
  have hR := θ.row_pos_of_column_pos_eq hscore _ hC
  rw [θ.row_eq_loop_of_no_offdiag_out _ p.sink_no_offdiag_out] at hR
  exact hR

theorem row_pos {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    0 < θ.row (p.node j) := by
  by_cases hj : j = Fin.last p.n
  · subst j
    exact θ.row_pos_of_weight_pos (p.sink_loop_pos hscore)
  · have hjlt : j.1 < p.n := by
      have hjle : j.1 ≤ p.n := by omega
      have hjne : j.1 ≠ p.n := by
        intro h
        apply hj
        ext
        simpa using h
      omega
    let k : Fin p.n := ⟨j.1, hjlt⟩
    have hk : k.castSucc = j := by ext; rfl
    rw [← hk]
    exact θ.row_pos_of_weight_pos (p.edge_pos k)

theorem column_pos {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    0 < θ.column (p.node j) :=
  θ.column_pos_of_row_pos_eq hscore _ (p.row_pos hscore j)

theorem ratio_pos {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    0 < p.ratio j := by
  unfold ratio
  exact div_pos (Real.sqrt_pos.2 (mul_pos (p.row_pos hscore j)
    (p.column_pos hscore j))) (p.column_pos hscore j)

theorem ratio_sq {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    p.ratio j ^ 2 = θ.row (p.node j) / θ.column (p.node j) := by
  unfold ratio
  have hC := ne_of_gt (p.column_pos hscore j)
  have hRC : 0 ≤ θ.row (p.node j) * θ.column (p.node j) :=
    mul_nonneg (θ.row_nonneg _) (θ.column_nonneg _)
  rw [div_pow, Real.sq_sqrt hRC]
  field_simp

theorem source_ratio_gt_one {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) : 1 < p.ratio 0 := by
  have hr := p.ratio_pos hscore 0
  have hsq := p.ratio_sq hscore 0
  have hdiv : 1 < θ.row (p.node 0) / θ.column (p.node 0) :=
    (one_lt_div (p.column_pos hscore 0)).2 p.source_column_lt_row
  nlinarith

theorem sink_ratio_lt_one {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) : p.ratio (Fin.last p.n) < 1 := by
  have hr := p.ratio_pos hscore (Fin.last p.n)
  have hsq := p.ratio_sq hscore (Fin.last p.n)
  have hdiv : θ.row (p.node (Fin.last p.n)) /
      θ.column (p.node (Fin.last p.n)) < 1 :=
    (div_lt_one (p.column_pos hscore (Fin.last p.n))).2 p.sink_row_lt_column
  nlinarith

/-- Every vertex on the extracted spine is strictly inside the label
interval.  The source and sink carry positive loops, hence are interior;
monotonicity then traps every intermediate vertex between them. -/
theorem label_mem_Ioo {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    θ.label (p.node j) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hsource : θ.label (p.node 0) ∈ Set.Ioo (-1 : ℝ) 1 :=
    θ.loop_label_mem_Ioo hscore _ (p.source_loop_pos hscore)
  have hsink : θ.label (p.node (Fin.last p.n)) ∈ Set.Ioo (-1 : ℝ) 1 :=
    θ.loop_label_mem_Ioo hscore _ (p.sink_loop_pos hscore)
  rcases p.ordered with hinc | hdec
  · have hmono : Monotone (fun k => θ.label (p.node k)) :=
      ((Fin.strictMono_iff_lt_succ.mpr hinc).monotone)
    exact ⟨lt_of_lt_of_le hsource.1 (hmono (Fin.zero_le j)),
      lt_of_le_of_lt (hmono (Fin.le_last j)) hsink.2⟩
  · have hanti : Antitone (fun k => θ.label (p.node k)) :=
      ((Fin.strictAnti_iff_succ_lt.mpr hdec).antitone)
    exact ⟨lt_of_lt_of_le hsink.1 (hanti (Fin.le_last j)),
      lt_of_le_of_lt (hanti (Fin.zero_le j)) hsource.2⟩

/-- The left square-root slope is the reciprocal-ratio junction term. -/
theorem leftSlope_eq_ratio {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    θ.leftSlope (p.node j) =
      s (θ.label (p.node j)) / (2 * p.ratio j) := by
  have hR : θ.row (p.node j) ≠ 0 := ne_of_gt (p.row_pos hscore j)
  have hC : θ.column (p.node j) ≠ 0 := ne_of_gt (p.column_pos hscore j)
  have hRC : 0 ≤ θ.row (p.node j) * θ.column (p.node j) :=
    mul_nonneg (θ.row_nonneg _) (θ.column_nonneg _)
  have hsqrt : Real.sqrt
      (θ.row (p.node j) * θ.column (p.node j)) ≠ 0 := by
    positivity
  have hsquare : Real.sqrt
      (θ.row (p.node j) * θ.column (p.node j)) ^ 2 =
        θ.row (p.node j) * θ.column (p.node j) :=
    Real.sq_sqrt hRC
  unfold CouplingTable.leftSlope ratio
  rw [if_neg hR]
  field_simp
  rw [hsquare]
  ring

/-- The right square-root slope is the forward-ratio junction term. -/
theorem rightSlope_eq_ratio {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin (p.n + 1)) :
    θ.rightSlope (p.node j) =
      s (θ.label (p.node j)) / 2 * p.ratio j := by
  have hC : θ.column (p.node j) ≠ 0 := ne_of_gt (p.column_pos hscore j)
  unfold CouplingTable.rightSlope ratio
  rw [if_neg hC]
  ring

/-- Tightness of a positive path cell is exactly the finite-spine value
recurrence. -/
theorem edge_value {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) (j : Fin p.n) :
    betaPV = d (θ.label (p.node j.castSucc)) (θ.label (p.node j.succ)) +
      s (θ.label (p.node j.castSucc)) / (2 * p.ratio j.castSucc) +
      s (θ.label (p.node j.succ)) / 2 * p.ratio j.succ := by
  have htight := θ.occupied_tight hscore (p.edge_pos j)
  rw [CouplingTable.gain, p.leftSlope_eq_ratio hscore,
    p.rightSlope_eq_ratio hscore] at htight
  exact htight.symm

/-- Tightness of the positive source loop gives the constant left-tail value
equation. -/
theorem left_value {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) :
    betaPV = d (θ.label (p.node 0)) (θ.label (p.node 0)) +
      s (θ.label (p.node 0)) / (2 * p.ratio 0) +
      s (θ.label (p.node 0)) / 2 * p.ratio 0 := by
  have htight := θ.occupied_tight hscore (p.source_loop_pos hscore)
  rw [CouplingTable.gain, p.leftSlope_eq_ratio hscore,
    p.rightSlope_eq_ratio hscore] at htight
  exact htight.symm

/-- Tightness of the positive sink loop gives the constant right-tail value
equation. -/
theorem right_value {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) :
    betaPV =
      d (θ.label (p.node (Fin.last p.n)))
        (θ.label (p.node (Fin.last p.n))) +
      s (θ.label (p.node (Fin.last p.n))) /
        (2 * p.ratio (Fin.last p.n)) +
      s (θ.label (p.node (Fin.last p.n))) / 2 *
        p.ratio (Fin.last p.n) := by
  have htight := θ.occupied_tight hscore (p.sink_loop_pos hscore)
  rw [CouplingTable.gain, p.leftSlope_eq_ratio hscore,
    p.rightSlope_eq_ratio hscore] at htight
  exact htight.symm

/-- The raw finite spine canonically associated with a support path.  Its
geometric tails are already square-summable because the source ratio is
greater than one and the sink ratio is less than one. -/
noncomputable def toFiniteSpineCore {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) : FiniteSpineCore where
  n := p.n
  n_pos := p.n_pos
  label j := θ.label (p.node j)
  ratio := p.ratio
  label_mem_Icc j := θ.label_mem (p.node j)
  ratio_pos := p.ratio_pos hscore
  left_ratio_gt_one := p.source_ratio_gt_one hscore
  right_ratio_lt_one := p.sink_ratio_lt_one hscore

/-- The extracted support path satisfies all value equations required by the
generic finite-window stationarity argument. -/
noncomputable def toValueSpine {θ : CouplingTable} (p : θ.SupportSpine)
    (hscore : θ.score = betaPV) : ValueSpine where
  toFiniteSpineCore := p.toFiniteSpineCore hscore
  label_mem_Ioo := p.label_mem_Ioo hscore
  left_value := p.left_value hscore
  edge_value := p.edge_value hscore
  right_value := p.right_value hscore

end SupportSpine

/-- Equality of a finite coupling table with the PV supremum would construct
the forbidden two-sided equality chain. -/
theorem equalityChainOfTable (θ : CouplingTable)
    (hscore : θ.score = betaPV) : Nonempty EqualityChain := by
  obtain ⟨p⟩ := θ.exists_supportSpine hscore
  exact (p.toValueSpine hscore).nonempty_equalityChain

/-- No finite coupling table attains the PV supremum. -/
theorem score_ne_betaPV (θ : CouplingTable) : θ.score ≠ betaPV := by
  intro hscore
  obtain ⟨q⟩ := θ.equalityChainOfTable hscore
  exact q.false

/-- Equivalently, every finite coupling table lies strictly below the PV
supremum. -/
theorem score_lt_betaPV (θ : CouplingTable) : θ.score < betaPV :=
  lt_of_le_of_ne (Ensemble.score_le_betaPV θ) θ.score_ne_betaPV

end CouplingTable
end I3322
