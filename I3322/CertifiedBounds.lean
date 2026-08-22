import I3322.PV
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Exact coarse bounds for the PV supremum

This file starts the end-to-end formalization of Appendix E.  The lower
bound is the exact length-29 rational certificate from equation (E2).
-/

namespace I3322

namespace CertifiedBounds

private noncomputable def lowerLabels : List ℝ :=
  [1,
   15 / 17, 15 / 17, 15 / 17, 15 / 17, 15 / 17, 15 / 17,
   15 / 17, 15 / 17, 15 / 17, 15 / 17, 15 / 17, 15 / 17,
   171 / 221, 5 / 13, -5 / 13, -171 / 221,
   -15 / 17, -15 / 17, -15 / 17, -15 / 17, -15 / 17, -15 / 17,
   -15 / 17, -15 / 17, -15 / 17, -15 / 17, -15 / 17, -15 / 17,
   -1]

private noncomputable def lowerAmplitudes : List ℝ :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 13, 12,
   13, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2]

private noncomputable def lowerLabel (i : ℕ) : ℝ :=
  lowerLabels.getD i 0

private noncomputable def lowerAmplitude (i : ℕ) : ℝ :=
  lowerAmplitudes.getD i 0

private theorem sqrt_15_17 : s (15 / 17 : ℝ) = 8 / 17 := by
  unfold s
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

private theorem sqrt_171_221 : s (171 / 221 : ℝ) = 140 / 221 := by
  unfold s
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

private theorem sqrt_5_13 : s (5 / 13 : ℝ) = 12 / 13 := by
  unfold s
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

private theorem sqrt_neg (c : ℝ) : s (-c) = s c := by
  simp [s]

/-- The exact length-29 chain used for the strict lower bound. -/
noncomputable def lowerCertificate : PVChain where
  n := 29
  n_pos := by norm_num
  label := lowerLabel
  amplitude := lowerAmplitude
  label_mem := by
    intro i hi
    interval_cases i <;> norm_num [lowerLabel, lowerLabels]
  leftEndpoint := by norm_num [lowerLabel, lowerLabels]
  rightEndpoint := by norm_num [lowerLabel, lowerLabels]
  amplitude_nonneg := by
    intro i hi
    interval_cases i <;> norm_num [lowerAmplitude, lowerAmplitudes]
  normSq_pos := by
    norm_num [lowerAmplitude, lowerAmplitudes, Finset.sum_range_succ]

theorem lowerCertificate_normSq : lowerCertificate.normSq = 2510 := by
  norm_num [PVChain.normSq, lowerCertificate, lowerAmplitude, lowerAmplitudes,
    Finset.sum_range_succ]

theorem lowerCertificate_value :
    lowerCertificate.value = 15324577 / 61295455 := by
  rw [PVChain.value, lowerCertificate_normSq]
  norm_num [PVChain.numerator, lowerCertificate, lowerLabel, lowerLabels,
    lowerAmplitude, lowerAmplitudes, d, sqrt_15_17, sqrt_171_221,
    sqrt_5_13, sqrt_neg, Finset.sum_range_succ]

theorem quarter_lt_lowerCertificate_value :
    (1 / 4 : ℝ) < lowerCertificate.value := by
  rw [lowerCertificate_value]
  norm_num

end CertifiedBounds
end I3322
