import I3322.PVSupremum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The equality-chain contradiction

This file formalizes the propagation and square-summability contradiction in
the last part of Lemma 6.  The two displayed recurrences are equations
(40)--(41) of the manuscript.
-/

namespace I3322

/-- A two-sided equality chain after endpoint exclusion and differentiation. -/
structure EqualityChain where
  label : ℤ → ℝ
  amplitude : ℤ → ℝ
  ratio : ℤ → ℝ
  label_mem : ∀ i, label i ∈ Set.Ioo (-1 : ℝ) 1
  amplitude_pos : ∀ i, 0 < amplitude i
  ratio_def : ∀ i, ratio i = amplitude (i + 1) / amplitude i
  ratio_pos : ∀ i, 0 < ratio i
  ratio_recurrence : ∀ i,
    betaPV = d (label (i - 1)) (label i) +
      s (label (i - 1)) / (2 * ratio (i - 1)) +
      s (label i) / 2 * ratio i
  label_recurrence : ∀ i,
    0 = label (i - 1) - 1 / 2 +
      (label (i + 1) + 1 / 2) * ratio i ^ 2 -
      label i / s (label i) * ratio i
  squareSummable : Summable (fun i => amplitude i ^ 2)
  tailLabel : ℝ
  tailRatio : ℝ
  tailRatio_gt_one : 1 < tailRatio
  tailEnd : ℤ
  left_tail_label : ∀ i ≤ tailEnd, label i = tailLabel
  left_tail_ratio : ∀ i < tailEnd, ratio i = tailRatio

namespace EqualityChain

theorem s_pos (q : EqualityChain) (i : ℤ) : 0 < s (q.label i) := by
  unfold s
  rcases q.label_mem i with ⟨hiL, hiR⟩
  apply Real.sqrt_pos.2
  have hp : 0 < (1 - q.label i) * (1 + q.label i) :=
    mul_pos (sub_pos.mpr hiR) (by linarith)
  nlinarith

/-- Equations (40)--(41) uniquely propagate a constant state by one step. -/
theorem propagate_one (q : EqualityChain) (i : ℤ)
    (hprev : q.label (i - 1) = q.tailLabel)
    (hcur : q.label i = q.tailLabel)
    (hrprev : q.ratio (i - 1) = q.tailRatio) :
    q.ratio i = q.tailRatio ∧ q.label (i + 1) = q.tailLabel := by
  let j := q.tailEnd - 1
  have hjm1 : j - 1 ≤ q.tailEnd := by dsimp [j]; omega
  have hj : j ≤ q.tailEnd := by dsimp [j]; omega
  have hjp1 : j + 1 ≤ q.tailEnd := by dsimp [j]; omega
  have hjlt : j < q.tailEnd := by dsimp [j]; omega
  have hjm1lt : j - 1 < q.tailEnd := by dsimp [j]; omega
  have hLj1 := q.left_tail_label (j - 1) hjm1
  have hLj := q.left_tail_label j hj
  have hLjp1 := q.left_tail_label (j + 1) hjp1
  have hRjm1 := q.left_tail_ratio (j - 1) hjm1lt
  have hRj := q.left_tail_ratio j hjlt
  have hbaseR := q.ratio_recurrence j
  have hstepR := q.ratio_recurrence i
  rw [hLj1, hLj, hRjm1, hRj] at hbaseR
  rw [hprev, hcur, hrprev] at hstepR
  have hs : 0 < s q.tailLabel := by
    rw [← hcur]
    exact q.s_pos i
  have hratio : q.ratio i = q.tailRatio := by
    nlinarith
  have hbaseL := q.label_recurrence j
  have hstepL := q.label_recurrence i
  rw [hLj1, hLj, hLjp1, hRj] at hbaseL
  rw [hprev, hcur, hratio] at hstepL
  have hk : 0 < q.tailRatio ^ 2 := sq_pos_of_pos (lt_trans zero_lt_one q.tailRatio_gt_one)
  refine ⟨hratio, ?_⟩
  nlinarith

/-- The constant left tail propagates through every position to its right. -/
theorem propagated (q : EqualityChain) :
    ∀ n : ℕ,
      q.label (q.tailEnd + (n : ℤ) - 1) = q.tailLabel ∧
      q.label (q.tailEnd + (n : ℤ)) = q.tailLabel ∧
        q.ratio (q.tailEnd + (n : ℤ) - 1) = q.tailRatio := by
  intro n
  induction n with
  | zero =>
      constructor
      · apply q.left_tail_label
        omega
      · constructor
        · simpa using q.left_tail_label q.tailEnd le_rfl
        · apply q.left_tail_ratio
          omega
  | succ n ih =>
      have hp := q.propagate_one (q.tailEnd + (n : ℤ)) ih.1 ih.2.1 ih.2.2
      have hminus : q.tailEnd + ((n + 1 : ℕ) : ℤ) - 1 =
          q.tailEnd + (n : ℤ) := by push_cast; ring
      have hplus : q.tailEnd + ((n + 1 : ℕ) : ℤ) =
          q.tailEnd + (n : ℤ) + 1 := by push_cast; ring
      constructor
      · rw [hminus]
        exact ih.2.1
      · constructor
        · rw [hplus]
          exact hp.2
        · rw [hminus]
          exact hp.1

theorem amplitude_geometric (q : EqualityChain) :
    ∀ n : ℕ,
      q.amplitude (q.tailEnd + (n : ℤ)) =
        q.tailRatio ^ n * q.amplitude q.tailEnd := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hr := (q.propagated (n + 1)).2.2
      have hdef := q.ratio_def (q.tailEnd + (n : ℤ))
      have hne : q.amplitude (q.tailEnd + (n : ℤ)) ≠ 0 :=
        ne_of_gt (q.amplitude_pos _)
      have hstep : q.amplitude (q.tailEnd + (n : ℤ) + 1) =
          q.tailRatio * q.amplitude (q.tailEnd + (n : ℤ)) := by
        have hidx : q.tailEnd + ((n + 1 : ℕ) : ℤ) - 1 =
            q.tailEnd + (n : ℤ) := by norm_num; omega
        rw [hidx] at hr
        rw [hr] at hdef
        field_simp at hdef
        linarith
      rw [show q.tailEnd + ((n + 1 : ℕ) : ℤ) =
          q.tailEnd + (n : ℤ) + 1 by norm_num; omega,
        hstep, ih, pow_succ]
      ring

/-- Lemma 6, final step: exact geometric growth with ratio greater than one
is incompatible with square summability. -/
theorem false (q : EqualityChain) : False := by
  let e : ℕ → ℤ := fun n => q.tailEnd + (n : ℤ)
  have heinj : Function.Injective e := by
    intro m n h
    dsimp [e] at h
    omega
  have hsum : Summable (fun n : ℕ => q.amplitude (e n) ^ 2) :=
    q.squareSummable.comp_injective heinj
  have hzero : Filter.Tendsto (fun n : ℕ => q.amplitude (e n) ^ 2)
      Filter.atTop (nhds 0) := hsum.tendsto_atTop_zero
  have ha : 0 < q.amplitude q.tailEnd ^ 2 := sq_pos_of_pos (q.amplitude_pos _)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      q.amplitude (e n) ^ 2 < q.amplitude q.tailEnd ^ 2 / 2 :=
    (tendsto_order.1 hzero).2 _ (by linarith)
  obtain ⟨n, hn⟩ := hevent.exists
  have hkpow : 1 ≤ q.tailRatio ^ n := by
    exact one_le_pow₀ (le_of_lt q.tailRatio_gt_one)
  have hgeom := q.amplitude_geometric n
  change q.amplitude (e n) = _ at hgeom
  have hlower : q.amplitude q.tailEnd ^ 2 ≤ q.amplitude (e n) ^ 2 := by
    rw [hgeom, mul_pow]
    have hkpow2 : 1 ≤ (q.tailRatio ^ n) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (q.amplitude q.tailEnd)]
  linarith

instance : IsEmpty EqualityChain := ⟨fun q => q.false.elim⟩

end EqualityChain
end I3322
