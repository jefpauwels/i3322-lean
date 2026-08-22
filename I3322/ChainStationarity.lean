import I3322.PVSupremum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One-label stationarity for a two-sided PV chain

Changing one label in a bi-infinite PV chain changes only the two adjacent
diagonal terms and their common junction term.  This file isolates that
finite-coordinate objective and proves its exact first-order condition.

The maximality hypothesis is stated as an inequality for all
admissible replacement labels.  It is the interface supplied by finite PV
truncations: every finitely perturbed truncation is bounded by `betaPV`, and
the boundary errors vanish for a square-summable chain.  No differentiation
of an infinite series is used below.
-/

namespace I3322
namespace ChainStationarity

/-- The three numerator terms which depend on the label at position `i`.
The amplitude `amplitude i` belongs to the edge from `label (i-1)` to
`label i`, matching the indexing in `EqualityChain`. -/
noncomputable def localLabelObjective
    (label amplitude : ℤ → ℝ) (i : ℤ) (x : ℝ) : ℝ :=
  d (label (i - 1)) x * amplitude i ^ 2 +
    d x (label (i + 1)) * amplitude (i + 1) ^ 2 +
    s x * amplitude i * amplitude (i + 1)

/-- `s(c)` is strictly positive at every interior label. -/
theorem s_pos_of_mem_Ioo {c : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < s c := by
  unfold s
  apply Real.sqrt_pos.2
  nlinarith [hc.1, hc.2]

/-- Derivative of `s(c) = sqrt (1-c²)` away from the endpoints. -/
theorem hasDerivAt_s {c : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt s (-c / s c) c := by
  have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * c) c := by
    convert (hasDerivAt_const (x := c) (c := (1 : ℝ))).sub
      ((hasDerivAt_id (x := c)).pow 2) using 1
    all_goals first | rfl | (norm_num [id_eq, div_eq_mul_inv] <;> ring)
  have hne : 1 - c ^ 2 ≠ 0 := by
    nlinarith [hc.1, hc.2]
  have hsqrt := hinner.sqrt hne
  unfold s
  convert hsqrt using 1
  field_simp

/-- Derivative in the second argument of the diagonal coefficient. -/
theorem hasDerivAt_d_right (a x : ℝ) :
    HasDerivAt (fun y : ℝ => d a y) (a - 1 / 2) x := by
  unfold d
  convert (((hasDerivAt_id (x := x)).const_mul a).add
    (((hasDerivAt_const (x := x) (c := a)).sub
      (hasDerivAt_id (x := x))).div_const 2)).sub_const 1 using 1
  all_goals first | rfl | (norm_num [id_eq, div_eq_mul_inv] <;> ring)

/-- Derivative in the first argument of the diagonal coefficient. -/
theorem hasDerivAt_d_left (b x : ℝ) :
    HasDerivAt (fun y : ℝ => d y b) (b + 1 / 2) x := by
  unfold d
  convert ((((hasDerivAt_id (x := x)).mul_const b).add
    (((hasDerivAt_id (x := x)).sub
      (hasDerivAt_const (x := x) (c := b))).div_const 2)).sub_const 1) using 1
  all_goals first | rfl | (norm_num [id_eq, div_eq_mul_inv] <;> ring)

/-- Exact derivative of the finite-coordinate objective. -/
theorem hasDerivAt_localLabelObjective
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (localLabelObjective label amplitude i)
      ((label (i - 1) - 1 / 2) * amplitude i ^ 2 +
        (label (i + 1) + 1 / 2) * amplitude (i + 1) ^ 2 -
        label i / s (label i) * amplitude i * amplitude (i + 1))
      (label i) := by
  have hleft := (hasDerivAt_d_right (label (i - 1)) (label i)).mul_const
    (amplitude i ^ 2)
  have hright := (hasDerivAt_d_left (label (i + 1)) (label i)).mul_const
    (amplitude (i + 1) ^ 2)
  have hjunction := ((hasDerivAt_s hi).mul_const (amplitude i)).mul_const
    (amplitude (i + 1))
  unfold localLabelObjective
  convert (hleft.add hright).add hjunction using 1
  all_goals first | rfl | (norm_num [id_eq, div_eq_mul_inv] <;> ring)

/-- A global bound on admissible one-label replacements makes the current
interior label a genuine local maximizer on `ℝ`. -/
theorem isLocalMax_localLabelObjective
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      localLabelObjective label amplitude i x ≤
        localLabelObjective label amplitude i (label i)) :
    IsLocalMax (localLabelObjective label amplitude i) (label i) := by
  filter_upwards [isOpen_Ioo.mem_nhds hi] with x hx
  exact hmax x ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- Finite-window bridge.  `windowNumerator N` is the numerator of the
unperturbed truncation and `windowNormSq N` its squared norm.  The first
hypothesis says the recurrence and square summability make its deficit from
`betaPV * windowNormSq N` tend to zero.  The second is exactly the finite PV
bound after replacing the single label by `x`; the displayed difference is
the only change in the numerator.

Taking the limit therefore gives genuine nonincrease of the three-term local
objective.  This lemma keeps all limiting arguments outside the subsequent
differentiation step. -/
theorem local_nonincrease_of_finite_windows
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (windowNumerator windowNormSq : ℕ → ℝ)
    (hdefect : Filter.Tendsto
      (fun N => betaPV * windowNormSq N - windowNumerator N)
      Filter.atTop (nhds 0))
    (hfinite : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ N,
      windowNumerator N +
          (localLabelObjective label amplitude i x -
            localLabelObjective label amplitude i (label i)) ≤
        betaPV * windowNormSq N) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      localLabelObjective label amplitude i x ≤
        localLabelObjective label amplitude i (label i) := by
  intro x hx
  have hdelta : ∀ N,
      localLabelObjective label amplitude i x -
          localLabelObjective label amplitude i (label i) ≤
        betaPV * windowNormSq N - windowNumerator N := by
    intro N
    linarith [hfinite x hx N]
  have hle :
      localLabelObjective label amplitude i x -
          localLabelObjective label amplitude i (label i) ≤ 0 :=
    ge_of_tendsto' hdefect hdelta
  linarith

/-- Undivided label stationarity.  This is the direct finite-coordinate
first variation before introducing amplitude ratios. -/
theorem weighted_stationarity
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      localLabelObjective label amplitude i x ≤
        localLabelObjective label amplitude i (label i)) :
    (label (i - 1) - 1 / 2) * amplitude i ^ 2 +
      (label (i + 1) + 1 / 2) * amplitude (i + 1) ^ 2 -
      label i / s (label i) * amplitude i * amplitude (i + 1) = 0 := by
  have hlocal := isLocalMax_localLabelObjective label amplitude i hi hmax
  have hzero := hlocal.deriv_eq_zero
  have hderiv := (hasDerivAt_localLabelObjective label amplitude i hi).deriv
  rw [hderiv] at hzero
  exact hzero

/-- Stationarity obtained directly from finite PV truncation bounds and a
vanishing boundary defect. -/
theorem weighted_stationarity_of_finite_windows
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1)
    (windowNumerator windowNormSq : ℕ → ℝ)
    (hdefect : Filter.Tendsto
      (fun N => betaPV * windowNormSq N - windowNumerator N)
      Filter.atTop (nhds 0))
    (hfinite : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ N,
      windowNumerator N +
          (localLabelObjective label amplitude i x -
            localLabelObjective label amplitude i (label i)) ≤
        betaPV * windowNormSq N) :
    (label (i - 1) - 1 / 2) * amplitude i ^ 2 +
      (label (i + 1) + 1 / 2) * amplitude (i + 1) ^ 2 -
      label i / s (label i) * amplitude i * amplitude (i + 1) = 0 := by
  apply weighted_stationarity label amplitude i hi
  exact local_nonincrease_of_finite_windows label amplitude i
    windowNumerator windowNormSq hdefect hfinite

/-- Exact ratio form of the label recurrence used by `EqualityChain`.
Both signs of the variation are legitimate because the current label is in
the open interval. -/
theorem label_stationarity
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1)
    (hamp : 0 < amplitude i)
    (hmax : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      localLabelObjective label amplitude i x ≤
        localLabelObjective label amplitude i (label i)) :
    0 = label (i - 1) - 1 / 2 +
      (label (i + 1) + 1 / 2) *
        (amplitude (i + 1) / amplitude i) ^ 2 -
      label i / s (label i) * (amplitude (i + 1) / amplitude i) := by
  have hweighted := weighted_stationarity label amplitude i hi hmax
  have hne : amplitude i ≠ 0 := ne_of_gt hamp
  have hsne : s (label i) ≠ 0 := ne_of_gt (s_pos_of_mem_Ioo hi)
  have hform :
      label (i - 1) - 1 / 2 +
          (label (i + 1) + 1 / 2) *
            (amplitude (i + 1) / amplitude i) ^ 2 -
          label i / s (label i) * (amplitude (i + 1) / amplitude i) =
        ((label (i - 1) - 1 / 2) * amplitude i ^ 2 +
          (label (i + 1) + 1 / 2) * amplitude (i + 1) ^ 2 -
          label i / s (label i) * amplitude i * amplitude (i + 1)) /
            amplitude i ^ 2 := by
    field_simp [hne, hsne]
  rw [hform, hweighted]
  simp

/-- Ratio-form stationarity directly from finite-window PV bounds.  This is
the complete reusable truncation-to-recurrence interface: upstream code only
has to identify its finite numerators and prove that their boundary deficit
tends to zero. -/
theorem label_stationarity_of_finite_windows
    (label amplitude : ℤ → ℝ) (i : ℤ)
    (hi : label i ∈ Set.Ioo (-1 : ℝ) 1)
    (hamp : 0 < amplitude i)
    (windowNumerator windowNormSq : ℕ → ℝ)
    (hdefect : Filter.Tendsto
      (fun N => betaPV * windowNormSq N - windowNumerator N)
      Filter.atTop (nhds 0))
    (hfinite : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ N,
      windowNumerator N +
          (localLabelObjective label amplitude i x -
            localLabelObjective label amplitude i (label i)) ≤
        betaPV * windowNormSq N) :
    0 = label (i - 1) - 1 / 2 +
      (label (i + 1) + 1 / 2) *
        (amplitude (i + 1) / amplitude i) ^ 2 -
      label i / s (label i) * (amplitude (i + 1) / amplitude i) := by
  apply label_stationarity label amplitude i hi hamp
  exact local_nonincrease_of_finite_windows label amplitude i
    windowNumerator windowNormSq hdefect hfinite

end ChainStationarity
end I3322
