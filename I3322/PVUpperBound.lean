import I3322.PV
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic upper bound for a PV cell

This is the pointwise inequality used in Appendix E to prove
`betaPV < 1/3`.
-/

namespace I3322

namespace PVUpperBound

theorem cell_le_golden (a b : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    d a b + (s a + s b) / 2 ≤ (Real.sqrt 5 - 1) / 4 := by
  let A := Real.arccos a
  let B := Real.arccos b
  let u := (A + B) / 2
  let v := (A - B) / 2
  let x := Real.sin u
  have hcosA : Real.cos A = a := Real.cos_arccos ha.1 ha.2
  have hcosB : Real.cos B = b := Real.cos_arccos hb.1 hb.2
  have hsinA : Real.sin A = s a := by
    simp [A, s, Real.sin_arccos]
  have hsinB : Real.sin B = s b := by
    simp [B, s, Real.sin_arccos]
  have hA : A = u + v := by
    simp only [u, v]
    ring
  have hB : B = u - v := by
    simp only [u, v]
    ring
  have hrewrite :
      d a b + (s a + s b) / 2 =
        -x ^ 2 - Real.sin v ^ 2 +
          x * (Real.cos v - Real.sin v) := by
    rw [← hsinA, ← hsinB, ← hcosA, ← hcosB, hA, hB]
    simp only [d, x, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]
  rw [hrewrite]
  have hcomplete :
      -x ^ 2 - Real.sin v ^ 2 + x * (Real.cos v - Real.sin v) ≤
        -Real.sin v ^ 2 + (Real.cos v - Real.sin v) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x - (Real.cos v - Real.sin v) / 2)]
  apply hcomplete.trans
  have htrig : Real.sin v ^ 2 + Real.cos v ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq v
  have hdoubleSin : Real.sin (2 * v) = 2 * Real.sin v * Real.cos v := by
    rw [Real.sin_two_mul]
  have hdoubleCos : Real.cos (2 * v) = 2 * Real.cos v ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have hform :
      -Real.sin v ^ 2 + (Real.cos v - Real.sin v) ^ 2 / 4 =
        (-1 + 2 * Real.cos (2 * v) - Real.sin (2 * v)) / 4 := by
    rw [hdoubleSin, hdoubleCos]
    nlinarith
  rw [hform]
  have hcircle : Real.sin (2 * v) ^ 2 + Real.cos (2 * v) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * v)
  have hsq :
      (2 * Real.cos (2 * v) - Real.sin (2 * v)) ^ 2 ≤ 5 := by
    nlinarith [sq_nonneg (Real.cos (2 * v) + 2 * Real.sin (2 * v))]
  have hlin :
      2 * Real.cos (2 * v) - Real.sin (2 * v) ≤ Real.sqrt 5 :=
    Real.le_sqrt_of_sq_le hsq
  linarith

theorem golden_lt_third : (Real.sqrt 5 - 1) / 4 < (1 / 3 : ℝ) := by
  have hsqrt : Real.sqrt 5 < (7 / 3 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  linarith

theorem cell_lt_third (a b : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    d a b + (s a + s b) / 2 < (1 / 3 : ℝ) :=
  (cell_le_golden a b ha hb).trans_lt golden_lt_third

private theorem neighbor_term_le_young (c x y : ℝ) :
    s c * x * y ≤ s c / 2 * (x ^ 2 + y ^ 2) := by
  have hs : 0 ≤ s c := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (x - y)]

private theorem neighbor_sum_le_cell_weights (p : PVChain) :
    (∑ i ∈ Finset.range (p.n - 1),
        s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)) ≤
      ∑ i ∈ Finset.range p.n,
        (s (p.label i) + s (p.label (i + 1))) / 2 * p.amplitude i ^ 2 := by
  let m := p.n - 1
  have hn : p.n = m + 1 := by
    dsimp [m]
    have hp : 0 < p.n := p.n_pos
    omega
  let f : ℕ → ℝ := fun i => s (p.label i) / 2 * p.amplitude i ^ 2
  let g : ℕ → ℝ := fun i => s (p.label (i + 1)) / 2 * p.amplitude i ^ 2
  have hyoung :
      (∑ i ∈ Finset.range m,
          s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)) ≤
        ∑ i ∈ Finset.range m, (g i + f (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    simpa [f, g, mul_add, mul_assoc] using
      neighbor_term_le_young (p.label (i + 1))
        (p.amplitude i) (p.amplitude (i + 1))
  have hf :
      (∑ i ∈ Finset.range (m + 1), f i) =
        f 0 + ∑ i ∈ Finset.range m, f (i + 1) := by
    simpa [Nat.add_comm] using (Finset.sum_range_add f 1 m)
  have hg :
      (∑ i ∈ Finset.range (m + 1), g i) =
        (∑ i ∈ Finset.range m, g i) + g m := by
    exact Finset.sum_range_succ g m
  rw [hn]
  change (∑ i ∈ Finset.range m,
      s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)) ≤ _
  apply hyoung.trans
  rw [Finset.sum_add_distrib]
  have hf0 : 0 ≤ f 0 := by
    dsimp [f]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) (sq_nonneg _)
  have hgm : 0 ≤ g m := by
    dsimp [g]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) (sq_nonneg _)
  change
    (∑ i ∈ Finset.range m, g i) + (∑ i ∈ Finset.range m, f (i + 1)) ≤
      ∑ i ∈ Finset.range (m + 1),
        (s (p.label i) + s (p.label (i + 1))) / 2 * p.amplitude i ^ 2
  have hsplit :
      (∑ i ∈ Finset.range (m + 1),
          (s (p.label i) + s (p.label (i + 1))) / 2 * p.amplitude i ^ 2) =
        (∑ i ∈ Finset.range (m + 1), f i) +
          ∑ i ∈ Finset.range (m + 1), g i := by
    simp only [f, g, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit, hf, hg]
  linarith

theorem numerator_le_golden_mul_normSq (p : PVChain) :
    p.numerator ≤ (Real.sqrt 5 - 1) / 4 * p.normSq := by
  let q : ℝ := (Real.sqrt 5 - 1) / 4
  have hneighbor := neighbor_sum_le_cell_weights p
  have hweighted :
      (∑ i ∈ Finset.range p.n,
          (d (p.label i) (p.label (i + 1)) +
              (s (p.label i) + s (p.label (i + 1))) / 2) *
            p.amplitude i ^ 2) ≤
        ∑ i ∈ Finset.range p.n, q * p.amplitude i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < p.n := Finset.mem_range.mp hi
    have hi_succ : i + 1 ≤ p.n := by omega
    have hcell := cell_le_golden (p.label i) (p.label (i + 1))
      (p.label_mem i (Nat.le_of_lt hi_lt)) (p.label_mem (i + 1) hi_succ)
    have hsquare : 0 ≤ p.amplitude i ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right hcell hsquare
  change
    (∑ i ∈ Finset.range p.n,
        d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2) +
      (∑ i ∈ Finset.range (p.n - 1),
        s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1)) ≤ _
  calc
    _ ≤ (∑ i ∈ Finset.range p.n,
          d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2) +
        ∑ i ∈ Finset.range p.n,
          (s (p.label i) + s (p.label (i + 1))) / 2 * p.amplitude i ^ 2 :=
      add_le_add_right hneighbor _
    _ = ∑ i ∈ Finset.range p.n,
        (d (p.label i) (p.label (i + 1)) +
            (s (p.label i) + s (p.label (i + 1))) / 2) *
          p.amplitude i ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range p.n, q * p.amplitude i ^ 2 := hweighted
    _ = (Real.sqrt 5 - 1) / 4 * p.normSq := by
      simp [q, PVChain.normSq, Finset.mul_sum]

theorem value_le_golden (p : PVChain) :
    p.value ≤ (Real.sqrt 5 - 1) / 4 := by
  rw [PVChain.value]
  exact (div_le_iff₀ p.normSq_pos').2 (numerator_le_golden_mul_normSq p)

theorem value_lt_third (p : PVChain) : p.value < (1 / 3 : ℝ) :=
  (value_le_golden p).trans_lt golden_lt_third

theorem values_bddAbove : BddAbove (Set.range PVChain.value) := by
  refine ⟨(1 / 3 : ℝ), ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (value_lt_third p).le

end PVUpperBound
end I3322
