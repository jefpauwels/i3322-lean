import I3322.Ensemble
import I3322.PVSupremum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From coupling tables to finite PV chains

This file sums the matching identities of `I3322.Ensemble`, applies the PV
supremum to every nonzero member of the ensemble, and removes the one missing
junction by sending the chain length to infinity.
-/

namespace I3322
namespace CouplingTable

open scoped BigOperators

/-- The cell (diagonal) part of the table score. -/
noncomputable def diagonalPart (θ : CouplingTable) : ℝ :=
  ∑ a, ∑ b, d (θ.label a) (θ.label b) * θ.weight a b

/-- The row/column square-root part of the table score. -/
noncomputable def junctionPart (θ : CouplingTable) : ℝ :=
  ∑ c, s (θ.label c) * Real.sqrt (θ.row c * θ.column c)

/-- The length-`N` ensemble quotient from equation (26). -/
noncomputable def finiteScore (θ : CouplingTable) (N : ℕ) : ℝ :=
  θ.diagonalPart + (((N - 1 : ℕ) : ℝ) / (N : ℝ)) * θ.junctionPart

theorem score_eq_parts (θ : CouplingTable) :
    θ.score = θ.diagonalPart + θ.junctionPart := rfl

theorem junctionPart_nonneg (θ : CouplingTable) : 0 ≤ θ.junctionPart := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem label_nonempty (θ : CouplingTable) : Nonempty θ.Label := by
  classical
  by_contra h
  haveI : IsEmpty θ.Label := not_nonempty_iff.mp h
  simpa using θ.totalWeight

/-- The uniform probability mass on one cell of the table's label set. -/
noncomputable def uniformWeight (θ : CouplingTable) : ℝ :=
  1 / (Fintype.card θ.Label : ℝ) ^ 2

theorem uniformWeight_pos (θ : CouplingTable) : 0 < θ.uniformWeight := by
  letI := θ.label_nonempty
  unfold uniformWeight
  positivity

/-- Mix a coupling table with the uniform table on the same labels. -/
noncomputable def regularize (θ : CouplingTable) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : CouplingTable where
  Label := θ.Label
  label := θ.label
  label_injective := θ.label_injective
  label_mem := θ.label_mem
  weight a b := (1 - ε) * θ.weight a b + ε * θ.uniformWeight
  weight_nonneg a b := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hε1) (θ.weight_nonneg a b))
    (mul_nonneg hε0 (le_of_lt θ.uniformWeight_pos))
  totalWeight := by
    classical
    letI := θ.label_nonempty
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [θ.totalWeight]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold uniformWeight
    have hc : (Fintype.card θ.Label : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem regularize_row (θ : CouplingTable) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (c : θ.Label) :
    (θ.regularize ε hε0 hε1).row c =
      (1 - ε) * θ.row c + ε / (Fintype.card θ.Label : ℝ) := by
  classical
  letI := θ.label_nonempty
  unfold row regularize uniformWeight
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card θ.Label : ℝ) ≠ 0 := by positivity
  field_simp

theorem regularize_column (θ : CouplingTable) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (c : θ.Label) :
    (θ.regularize ε hε0 hε1).column c =
      (1 - ε) * θ.column c + ε / (Fintype.card θ.Label : ℝ) := by
  classical
  letI := θ.label_nonempty
  unfold column regularize uniformWeight
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card θ.Label : ℝ) ≠ 0 := by positivity
  field_simp

theorem regularize_row_pos (θ : CouplingTable) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (c : θ.Label) :
    0 < (θ.regularize ε (le_of_lt hε0) hε1).row c := by
  rw [regularize_row]
  have hcard : (0 : ℝ) < Fintype.card θ.Label := by
    exact_mod_cast Fintype.card_pos_iff.mpr θ.label_nonempty
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hε1) (θ.row_nonneg c))
    (div_pos hε0 hcard)

theorem regularize_column_pos (θ : CouplingTable) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (c : θ.Label) :
    0 < (θ.regularize ε (le_of_lt hε0) hε1).column c := by
  rw [regularize_column]
  have hcard : (0 : ℝ) < Fintype.card θ.Label := by
    exact_mod_cast Fintype.card_pos_iff.mpr θ.label_nonempty
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hε1) (θ.column_nonneg c))
    (div_pos hε0 hcard)

namespace Ensemble

theorem sum_openNormSq (θ : CouplingTable) {N : ℕ} (E : Ensemble θ N)
    (hdiag : E.DiagonalMatches) :
    ∑ γ, openNormSq (E.chain γ) = N := by
  classical
  unfold openNormSq
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin N, ∑ γ, (E.chain γ).amplitude i ^ 2) =
        ∑ i : Fin N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := hdiag i (fun _ _ => 1)
      simpa [θ.totalWeight] using h
    _ = N := by simp

theorem sum_openNumerator (θ : CouplingTable) {N : ℕ} (E : Ensemble θ N)
    (hdiag : E.DiagonalMatches) (hjunc : E.JunctionMatches) :
    ∑ γ, openNumerator (E.chain γ) =
      (N : ℝ) * θ.diagonalPart + ((N - 1 : ℕ) : ℝ) * θ.junctionPart := by
  classical
  unfold openNumerator
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    calc
      (∑ i : Fin N, ∑ γ,
          d (θ.label ((E.chain γ).label i.castSucc))
              (θ.label ((E.chain γ).label i.succ)) *
            (E.chain γ).amplitude i ^ 2) =
          ∑ i : Fin N, θ.diagonalPart := by
        apply Finset.sum_congr rfl
        intro i _
        exact hdiag i (fun a b => d (θ.label a) (θ.label b))
      _ = (N : ℝ) * θ.diagonalPart := by simp
  · rw [Finset.sum_comm]
    calc
      (∑ i : Fin (N - 1), ∑ γ,
          s (θ.label ((E.chain γ).label ⟨i + 1, by omega⟩)) *
            (E.chain γ).amplitude ⟨i, by omega⟩ *
              (E.chain γ).amplitude ⟨i + 1, by omega⟩) =
          ∑ i : Fin (N - 1), θ.junctionPart := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [junctionPart, mul_assoc] using
          (hjunc i (by omega) (fun c => s (θ.label c)))
      _ = ((N - 1 : ℕ) : ℝ) * θ.junctionPart := by simp

theorem openNumerator_le_beta_mul_norm (θ : CouplingTable) {N : ℕ}
    (q : OpenChain θ N) (hamp : ∀ i, 0 ≤ q.amplitude i) :
    openNumerator q ≤ betaPV * openNormSq q := by
  have hnorm_nonneg : 0 ≤ openNormSq q := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hnorm_nonneg.eq_or_lt with hzero | hpos
  · have hamp_zero : ∀ i, q.amplitude i = 0 := by
      intro i
      have hi : q.amplitude i ^ 2 ≤ openNormSq q := by
        unfold openNormSq
        exact Finset.single_le_sum (fun j _ => sq_nonneg (q.amplitude j))
          (Finset.mem_univ i)
      rw [← hzero] at hi
      nlinarith [sq_nonneg (q.amplitude i)]
    rw [← hzero]
    simp only [mul_zero]
    unfold openNumerator
    simp [hamp_zero]
  · let p : PVChain := openToPV q hamp hpos
    have hpv : p.value ≤ betaPV := pvValue_le_betaPV p
    rw [PVChain.value, show p.numerator = openNumerator q by
      exact openToPV_numerator q hamp hpos,
      show p.normSq = openNormSq q by exact openToPV_normSq q hamp hpos] at hpv
    exact (div_le_iff₀ hpos).mp hpv

theorem finiteScore_le_betaPV_of_positive (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c)
    (N : ℕ) (hN : 0 < N) :
    θ.finiteScore N ≤ betaPV := by
  classical
  let E := walkEnsemble θ N hN
  have hdiag : E.DiagonalMatches :=
    walkEnsemble_diagonalMatches θ hrow hcolumn N hN
  have hjunc : E.JunctionMatches :=
    walkEnsemble_junctionMatches θ hrow hcolumn N hN
  have hamp : E.AmplitudesNonnegative :=
    walkEnsemble_amplitudesNonnegative θ N hN
  have hsum :
      ∑ γ, openNumerator (E.chain γ) ≤
        ∑ γ, betaPV * openNormSq (E.chain γ) := by
    exact Finset.sum_le_sum fun γ _ =>
      openNumerator_le_beta_mul_norm θ (E.chain γ) (hamp γ)
  rw [sum_openNumerator θ E hdiag hjunc, ← Finset.mul_sum,
    sum_openNormSq θ E hdiag] at hsum
  unfold finiteScore
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    θ.diagonalPart + ((↑(N - 1) : ℝ) / (N : ℝ)) * θ.junctionPart =
        ((N : ℝ) * θ.diagonalPart + (↑(N - 1) : ℝ) * θ.junctionPart) /
          (N : ℝ) := by field_simp
    _ ≤ (betaPV * (N : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hNr)
    _ = betaPV := by field_simp

theorem score_le_betaPV_of_positive (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c) :
    θ.score ≤ betaPV := by
  rw [score_eq_parts]
  by_contra h
  have hgap : 0 < θ.diagonalPart + θ.junctionPart - betaPV := by
    exact sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨N : ℕ, hNlarge : θ.junctionPart /
      (θ.diagonalPart + θ.junctionPart - betaPV) < N⟩ :=
    exists_nat_gt (θ.junctionPart /
      (θ.diagonalPart + θ.junctionPart - betaPV))
  have hratio_nonneg : 0 ≤ θ.junctionPart /
      (θ.diagonalPart + θ.junctionPart - betaPV) :=
    div_nonneg θ.junctionPart_nonneg (le_of_lt hgap)
  have hN : 0 < N := by
    have : (0 : ℝ) < N := hratio_nonneg.trans_lt hNlarge
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : θ.junctionPart / (N : ℝ) <
      θ.diagonalPart + θ.junctionPart - betaPV := by
    rw [div_lt_iff₀ hNr]
    have := (div_lt_iff₀ hgap).mp hNlarge
    nlinarith
  have hfinite := finiteScore_le_betaPV_of_positive θ hrow hcolumn N hN
  unfold finiteScore at hfinite
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hfinite
  have hform :
      θ.diagonalPart + (((N : ℝ) - 1) / (N : ℝ)) * θ.junctionPart =
        θ.diagonalPart + θ.junctionPart - θ.junctionPart / (N : ℝ) := by
    field_simp
    ring
  rw [hform] at hfinite
  linarith

/-- Lemma 4 of the manuscript: every finite coupling table is bounded by the
PV supremum.  Vanishing marginals are removed by uniform regularization; only
the table scores, not any infinite chain, pass to the limit. -/
theorem score_le_betaPV (θ : CouplingTable) : θ.score ≤ betaPV := by
  classical
  letI := θ.label_nonempty
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hεle : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp [ε]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  let F : ℝ → ℝ := fun t =>
    (∑ a, ∑ b,
      d (θ.label a) (θ.label b) *
        ((1 - t) * θ.weight a b + t * θ.uniformWeight)) +
      ∑ c, s (θ.label c) * Real.sqrt
        (((1 - t) * θ.row c + t / (Fintype.card θ.Label : ℝ)) *
          ((1 - t) * θ.column c + t / (Fintype.card θ.Label : ℝ)))
  have hreg (n : ℕ) :
      (θ.regularize (ε n) (le_of_lt (hεpos n)) (hεle n)).score = F (ε n) := by
    unfold score
    change
      (∑ a, ∑ b,
        d (θ.label a) (θ.label b) *
          ((1 - ε n) * θ.weight a b + ε n * θ.uniformWeight)) +
        ∑ c, s (θ.label c) * Real.sqrt
          ((θ.regularize (ε n) (le_of_lt (hεpos n)) (hεle n)).row c *
            (θ.regularize (ε n) (le_of_lt (hεpos n)) (hεle n)).column c) = _
    simp_rw [regularize_row, regularize_column]
    rfl
  have hF0 : F 0 = θ.score := by
    simp [F, score, row, column]
  have hcontinuous : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0))
  have hlimit : Filter.Tendsto
      (fun n => (θ.regularize (ε n) (le_of_lt (hεpos n)) (hεle n)).score)
      Filter.atTop (nhds θ.score) := by
    have hcomp := hcontinuous.tendsto.comp hεlim
    simpa [Function.comp_def, hreg, hF0] using hcomp
  exact le_of_tendsto' hlimit (fun n => by
    let θn := θ.regularize (ε n) (le_of_lt (hεpos n)) (hεle n)
    exact score_le_betaPV_of_positive θn
      (fun c => regularize_row_pos θ (ε n) (hεpos n) (hεle n) c)
      (fun c => regularize_column_pos θ (ε n) (hεpos n) (hεle n) c))

end Ensemble
end CouplingTable
end I3322
