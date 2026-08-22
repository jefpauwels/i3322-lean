import Mathlib.Algebra.BigOperators.Field
import I3322.CouplingTable

/-!
# Finite-chain ensembles

This file formalizes the Markov-walk construction from Appendix D of the
manuscript.  The matching conditions are stated as identities against an
arbitrary test function.  This is equivalent to the cell-by-cell form in the
paper, and makes the induction which appends one edge to every chain quite
transparent.
-/

namespace I3322
namespace CouplingTable

open scoped BigOperators

/-- An unnormalised open PV chain with `N` amplitudes and `N+1` table labels. -/
structure OpenChain (θ : CouplingTable) (N : ℕ) where
  label : Fin (N + 1) → θ.Label
  amplitude : Fin N → ℝ

/-- A finite ensemble of open chains. -/
structure Ensemble (θ : CouplingTable) (N : ℕ) where
  Index : Type
  [fintypeIndex : Fintype Index]
  chain : Index → OpenChain θ N

attribute [instance] Ensemble.fintypeIndex

namespace Ensemble

/-- Extend a finite vector to a total function on natural indices. -/
def natExtend {α : Type} {n : ℕ} (v : Fin n → α) (fallback : α) (i : ℕ) : α :=
  if h : i < n then v ⟨i, h⟩ else fallback

@[simp] theorem natExtend_apply_fin {α : Type} {n : ℕ} (v : Fin n → α)
    (fallback : α) (i : Fin n) : natExtend v fallback i = v i := by
  simp [natExtend, i.isLt]

/-- The diagonal matching identity, tested against an arbitrary function of a cell. -/
def DiagonalMatches (θ : CouplingTable) {N : ℕ} (E : Ensemble θ N) : Prop :=
  ∀ i : Fin N, ∀ f : θ.Label → θ.Label → ℝ,
    (∑ γ, f ((E.chain γ).label i.castSucc) ((E.chain γ).label i.succ) *
      (E.chain γ).amplitude i ^ 2) =
      ∑ a, ∑ b, f a b * θ.weight a b

/-- The junction matching identity, tested against an arbitrary function of the shared label. -/
def JunctionMatches (θ : CouplingTable) {N : ℕ} (E : Ensemble θ N) : Prop :=
  ∀ i : ℕ, ∀ hi : i + 1 < N, ∀ f : θ.Label → ℝ,
    (∑ γ, f ((E.chain γ).label ⟨i + 1, by omega⟩) *
      ((E.chain γ).amplitude ⟨i, by omega⟩ *
        (E.chain γ).amplitude ⟨i + 1, hi⟩)) =
      ∑ c, f c * Real.sqrt (θ.row c * θ.column c)

/-- All amplitudes in an ensemble are nonnegative. -/
def AmplitudesNonnegative (θ : CouplingTable) {N : ℕ} (E : Ensemble θ N) : Prop :=
  ∀ γ i, 0 ≤ (E.chain γ).amplitude i

/-- Squared norm of an open chain. -/
noncomputable def openNormSq {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) : ℝ :=
  ∑ i, q.amplitude i ^ 2

/-- Numerator carried by the table-labelled part of an open chain. -/
noncomputable def openNumerator {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) : ℝ :=
  (∑ i : Fin N,
      d (θ.label (q.label i.castSucc)) (θ.label (q.label i.succ)) *
        q.amplitude i ^ 2) +
    ∑ i : Fin (N - 1),
      s (θ.label (q.label ⟨i + 1, by omega⟩)) *
        q.amplitude ⟨i, by omega⟩ * q.amplitude ⟨i + 1, by omega⟩

/-- The labels of an open chain padded by the required endpoints `1` and `-1`. -/
noncomputable def paddedLabels {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) : Fin (N + 3) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun i => θ.label (q.label i)) (-1))

/-- The amplitudes of an open chain padded by a zero at each end. -/
noncomputable def paddedAmplitudes {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) : Fin (N + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc q.amplitude 0)

theorem sum_paddedAmplitudes_sq {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) :
    (∑ i, paddedAmplitudes q i ^ 2) = ∑ i, q.amplitude i ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [paddedAmplitudes, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  norm_num

@[simp] theorem natPaddedAmplitude_zero {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) :
    natExtend (paddedAmplitudes q) 0 0 = 0 := by
  simp [natExtend, paddedAmplitudes]

@[simp] theorem natPaddedAmplitude_succ {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) (i : Fin N) :
    natExtend (paddedAmplitudes q) 0 (i + 1) = q.amplitude i := by
  rw [natExtend]
  simp only [dif_pos (by omega : (i : ℕ) + 1 < N + 2)]
  change paddedAmplitudes q i.castSucc.succ = q.amplitude i
  simp [paddedAmplitudes]

@[simp] theorem natPaddedAmplitude_last {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) :
    natExtend (paddedAmplitudes q) 0 (N + 1) = 0 := by
  rw [natExtend]
  simp only [dif_pos (by omega : N + 1 < N + 2)]
  change paddedAmplitudes q (Fin.last (N + 1)) = 0
  simp [paddedAmplitudes]

@[simp] theorem natPaddedLabel_succ {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) (i : Fin (N + 1)) :
    natExtend (paddedLabels q) 0 (i + 1) = θ.label (q.label i) := by
  rw [natExtend]
  simp only [dif_pos (by omega : (i : ℕ) + 1 < N + 3)]
  change paddedLabels q i.castSucc.succ = θ.label (q.label i)
  simp [paddedLabels]

/-- Padding turns every nonzero, nonnegative open chain into a PV chain without
changing its quotient. -/
noncomputable def openToPV {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) (hamp : ∀ i, 0 ≤ q.amplitude i)
    (hnorm : 0 < openNormSq q) : PVChain where
  n := N + 2
  n_pos := by omega
  label := natExtend (paddedLabels q) 0
  amplitude := natExtend (paddedAmplitudes q) 0
  label_mem := by
    intro i hi
    have hi' : i < N + 3 := by omega
    rw [natExtend]
    simp only [dif_pos hi']
    let k : Fin (N + 3) := ⟨i, hi'⟩
    change (paddedLabels q k) ∈ Set.Icc (-1 : ℝ) 1
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [paddedLabels]
    · refine Fin.lastCases ?_ (fun m => ?_) j
      · simp [paddedLabels]
      · simpa [paddedLabels] using θ.label_mem (q.label m)
  leftEndpoint := by simp [natExtend, paddedLabels]
  rightEndpoint := by
    rw [natExtend]
    simp only [dif_pos (by omega : N + 2 < N + 3)]
    change paddedLabels q (Fin.last (N + 2)) = -1
    simp [paddedLabels]
  amplitude_nonneg := by
    intro i hi
    rw [natExtend]
    simp only [dif_pos hi]
    let k : Fin (N + 2) := ⟨i, hi⟩
    change 0 ≤ paddedAmplitudes q k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [paddedAmplitudes]
    · refine Fin.lastCases ?_ (fun m => ?_) j
      · simp [paddedAmplitudes]
      · simpa [paddedAmplitudes] using hamp m
  normSq_pos := by
    rw [Finset.sum_range]
    simp only [natExtend_apply_fin]
    change 0 < ∑ i, paddedAmplitudes q i ^ 2
    rw [sum_paddedAmplitudes_sq]
    exact hnorm

theorem openToPV_normSq {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) (hamp : ∀ i, 0 ≤ q.amplitude i)
    (hnorm : 0 < openNormSq q) :
    (openToPV q hamp hnorm).normSq = openNormSq q := by
  rw [PVChain.normSq_eq_fin_sum]
  simp only [openToPV, natExtend_apply_fin]
  change (∑ i, paddedAmplitudes q i ^ 2) = openNormSq q
  rw [sum_paddedAmplitudes_sq]
  rfl

theorem openToPV_numerator {θ : CouplingTable} {N : ℕ}
    (q : OpenChain θ N) (hamp : ∀ i, 0 ≤ q.amplitude i)
    (hnorm : 0 < openNormSq q) :
    (openToPV q hamp hnorm).numerator = openNumerator q := by
  cases N with
  | zero =>
      simp [openNormSq] at hnorm
  | succ n =>
      rw [PVChain.numerator_eq_fin_sums]
      simp only [openToPV]
      unfold openNumerator
      let L : ℕ → ℝ := natExtend (paddedLabels q) 0
      let A : ℕ → ℝ := natExtend (paddedAmplitudes q) 0
      have hdiag :
          (∑ x : Fin (n + 3), d (L x) (L (x + 1)) * A x ^ 2) =
            ∑ i : Fin (n + 1),
              d (θ.label (q.label i.castSucc)) (θ.label (q.label i.succ)) *
                q.amplitude i ^ 2 := by
        rw [Fin.sum_univ_succ]
        have hA0 : A 0 = 0 := by exact natPaddedAmplitude_zero q
        have hA0' : A (↑(0 : Fin (n + 3))) = 0 := by simpa using hA0
        rw [hA0']
        norm_num
        rw [Fin.sum_univ_castSucc]
        have hAend : A ((Fin.last (n + 1) : ℕ) + 1) = 0 := by
          simpa [A] using (natPaddedAmplitude_last q)
        rw [hAend]
        ring_nf
        apply Finset.sum_congr rfl
        intro i _
        have hA : A (1 + (i.castSucc : ℕ)) = q.amplitude i := by
          simpa [A, Nat.add_comm] using (natPaddedAmplitude_succ q i)
        have hL : L (1 + (i.castSucc : ℕ)) = θ.label (q.label i.castSucc) := by
          simpa [L, Nat.add_comm] using (natPaddedLabel_succ q i.castSucc)
        have hL' : L (2 + (i.castSucc : ℕ)) = θ.label (q.label i.succ) := by
          simpa [L, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (natPaddedLabel_succ q i.succ)
        rw [hA, hL, hL']
      have hjunc :
          (∑ x : Fin (n + 2), s (L (x + 1)) * A x * A (x + 1)) =
            ∑ i : Fin n,
              s (θ.label (q.label ⟨i + 1, by omega⟩)) *
                q.amplitude ⟨i, by omega⟩ * q.amplitude ⟨i + 1, by omega⟩ := by
        rw [Fin.sum_univ_succ]
        have hA0 : A 0 = 0 := by exact natPaddedAmplitude_zero q
        have hA0' : A (↑(0 : Fin (n + 2))) = 0 := by simpa using hA0
        rw [hA0']
        ring_nf
        rw [Fin.sum_univ_castSucc]
        have hAend : A (1 + ((Fin.last n).succ : ℕ)) = 0 := by
          simpa [A, Nat.add_comm] using (natPaddedAmplitude_last q)
        rw [hAend]
        simp only [mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        have hA : A (i.castSucc.succ) = q.amplitude i.castSucc := by
          simpa [A] using (natPaddedAmplitude_succ q i.castSucc)
        have hA' : A (1 + (i.castSucc.succ : ℕ)) = q.amplitude i.succ := by
          simpa [A, Nat.add_comm] using (natPaddedAmplitude_succ q i.succ)
        have hL : L (1 + (i.castSucc.succ : ℕ)) =
            θ.label (q.label i.succ.castSucc) := by
          simpa [L, Nat.add_comm] using (natPaddedLabel_succ q i.succ.castSucc)
        rw [hA, hA', hL]
        have hidx0 : i.castSucc = (⟨i, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        have hidx1 : i.succ = (⟨1 + (i : ℕ), by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          change (i : ℕ) + 1 = 1 + (i : ℕ)
          omega
        have hlidx : i.succ.castSucc =
            (⟨1 + (i : ℕ), by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          change (i : ℕ) + 1 = 1 + (i : ℕ)
          omega
        rw [hidx0, hlidx, hidx1]
      change
        (∑ x : Fin (n + 3), d (L x) (L (x + 1)) * A x ^ 2) +
          (∑ x : Fin (n + 2), s (L (x + 1)) * A x * A (x + 1)) = _
      rw [hdiag, hjunc]
      rfl

/-- The one-edge ensemble: one chain for every table cell. -/
noncomputable def one (θ : CouplingTable) : Ensemble θ 1 where
  Index := θ.Label × θ.Label
  chain γ :=
    { label := ![γ.1, γ.2]
      amplitude := fun _ => Real.sqrt (θ.weight γ.1 γ.2) }

theorem one_amplitudesNonnegative (θ : CouplingTable) :
    (one θ).AmplitudesNonnegative := by
  intro γ i
  exact Real.sqrt_nonneg _

theorem one_diagonalMatches (θ : CouplingTable) : (one θ).DiagonalMatches := by
  classical
  intro i f
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ γ : θ.Label × θ.Label,
    f γ.1 γ.2 * Real.sqrt (θ.weight γ.1 γ.2) ^ 2) = _
  simp_rw [Real.sq_sqrt (θ.weight_nonneg _ _)]
  exact Fintype.sum_prod_type _

theorem one_junctionMatches (θ : CouplingTable) : (one θ).JunctionMatches := by
  intro i hi
  omega

/-- Every row-normalized transition has total squared square-root weight one. -/
theorem sum_sq_sqrt_weight_div_row (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (c : θ.Label) :
    ∑ b, Real.sqrt (θ.weight c b / θ.row c) ^ 2 = 1 := by
  classical
  rw [show (∑ b, Real.sqrt (θ.weight c b / θ.row c) ^ 2) =
      ∑ b, θ.weight c b / θ.row c by
    apply Finset.sum_congr rfl
    intro b _
    rw [Real.sq_sqrt]
    exact div_nonneg (θ.weight_nonneg _ _) (le_of_lt (hrow c))]
  rw [← Finset.sum_div]
  change θ.row c / θ.row c = 1
  exact div_self (ne_of_gt (hrow c))

/-- Every column-normalized transition has total squared square-root weight one. -/
theorem sum_sq_sqrt_weight_div_column (θ : CouplingTable)
    (hcolumn : ∀ c, 0 < θ.column c) (c : θ.Label) :
    ∑ a, Real.sqrt (θ.weight a c / θ.column c) ^ 2 = 1 := by
  classical
  rw [show (∑ a, Real.sqrt (θ.weight a c / θ.column c) ^ 2) =
      ∑ a, θ.weight a c / θ.column c by
    apply Finset.sum_congr rfl
    intro a _
    rw [Real.sq_sqrt]
    exact div_nonneg (θ.weight_nonneg _ _) (le_of_lt (hcolumn c))]
  rw [← Finset.sum_div]
  change θ.column c / θ.column c = 1
  exact div_self (ne_of_gt (hcolumn c))

/-- The square-root identity at a newly-created junction. -/
theorem sqrt_transition_mul (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c)
    (c b : θ.Label) :
    Real.sqrt (θ.weight c b / θ.row c) *
        Real.sqrt (θ.weight c b / θ.column c) =
      θ.weight c b / Real.sqrt (θ.row c * θ.column c) := by
  have hw : 0 ≤ θ.weight c b := θ.weight_nonneg _ _
  have hr : 0 < θ.row c := hrow c
  have hc : 0 < θ.column c := hcolumn c
  rw [Real.sqrt_div hw, Real.sqrt_div hw]
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hw]
  rw [← Real.sqrt_mul (le_of_lt hr)]

/-- Appending one label to every chain, with the two transition normalizations
from Appendix D. -/
noncomputable def extend (θ : CouplingTable) {n : ℕ} (E : Ensemble θ (n + 1)) :
    Ensemble θ (n + 2) where
  Index := E.Index × θ.Label
  chain γ :=
    let old := E.chain γ.1
    let c := old.label (Fin.last (n + 1))
    let b := γ.2
    { label := Fin.snoc old.label b
      amplitude := Fin.snoc
        (fun i => old.amplitude i * Real.sqrt (θ.weight c b / θ.row c))
        (old.amplitude (Fin.last n) * Real.sqrt (θ.weight c b / θ.column c)) }

theorem extend_amplitudesNonnegative (θ : CouplingTable) {n : ℕ}
    (E : Ensemble θ (n + 1)) (hE : E.AmplitudesNonnegative) :
    (extend θ E).AmplitudesNonnegative := by
  intro γ i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [extend, Fin.snoc_last] using
      mul_nonneg (hE γ.1 (Fin.last n)) (Real.sqrt_nonneg
        (θ.weight ((E.chain γ.1).label (Fin.last (n + 1))) γ.2 /
          θ.column ((E.chain γ.1).label (Fin.last (n + 1)))))
  · simpa only [extend, Fin.snoc_castSucc] using
      mul_nonneg (hE γ.1 j) (Real.sqrt_nonneg
        (θ.weight ((E.chain γ.1).label (Fin.last (n + 1))) γ.2 /
          θ.row ((E.chain γ.1).label (Fin.last (n + 1)))))

/-- The last squared amplitudes of a matching ensemble have the column
marginal as their label distribution. -/
theorem terminal_moment (θ : CouplingTable) {n : ℕ} (E : Ensemble θ (n + 1))
    (hdiag : E.DiagonalMatches) (g : θ.Label → ℝ) :
    (∑ γ, g ((E.chain γ).label (Fin.last (n + 1))) *
      (E.chain γ).amplitude (Fin.last n) ^ 2) =
      ∑ c, g c * θ.column c := by
  have h := hdiag (Fin.last n) (fun _ c => g c)
  simpa [Fin.last, Fin.castSucc, Fin.succ] using h.trans (by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.mul_sum]
    rfl)

/-- Appending a normalized step preserves the diagonal cell moments and
creates the correct moment at the new last position. -/
theorem extend_diagonalMatches (θ : CouplingTable) {n : ℕ}
    (E : Ensemble θ (n + 1)) (hdiag : E.DiagonalMatches)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c) :
    (extend θ E).DiagonalMatches := by
  classical
  intro i f
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extend]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last]
    change (∑ γ : E.Index × θ.Label,
      f ((E.chain γ.1).label (Fin.last (n + 1))) γ.2 *
        ((E.chain γ.1).amplitude (Fin.last n) *
          Real.sqrt (θ.weight ((E.chain γ.1).label (Fin.last (n + 1))) γ.2 /
            θ.column ((E.chain γ.1).label (Fin.last (n + 1))))) ^ 2) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    simp_rw [Real.sq_sqrt (div_nonneg (θ.weight_nonneg _ _)
      (le_of_lt (hcolumn _)))]
    let g : θ.Label → ℝ := fun c =>
      ∑ b, f c b * (θ.weight c b / θ.column c)
    calc
      (∑ a, ∑ b,
          f ((E.chain a).label (Fin.last (n + 1))) b *
            ((E.chain a).amplitude (Fin.last n) ^ 2 *
              (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                θ.column ((E.chain a).label (Fin.last (n + 1)))))) =
          ∑ a, g ((E.chain a).label (Fin.last (n + 1))) *
            (E.chain a).amplitude (Fin.last n) ^ 2 := by
              apply Finset.sum_congr rfl
              intro a _
              dsimp [g]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = ∑ c, g c * θ.column c := terminal_moment θ E hdiag g
      _ = ∑ a, ∑ b, f a b * θ.weight a b := by
        dsimp [g]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
        have hc : θ.column c ≠ 0 := ne_of_gt (hcolumn c)
        apply Finset.sum_congr rfl
        intro b _
        field_simp
  · simp only [extend]
    rw [← Fin.castSucc_succ]
    simp only [Fin.snoc_castSucc]
    change (∑ γ : E.Index × θ.Label,
      f ((E.chain γ.1).label j.castSucc) ((E.chain γ.1).label j.succ) *
        ((E.chain γ.1).amplitude j *
          Real.sqrt (θ.weight ((E.chain γ.1).label (Fin.last (n + 1))) γ.2 /
            θ.row ((E.chain γ.1).label (Fin.last (n + 1))))) ^ 2) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    calc
      (∑ a, ∑ b,
          f ((E.chain a).label (Fin.castSucc j)) ((E.chain a).label (Fin.succ j)) *
            ((E.chain a).amplitude j ^ 2 *
              Real.sqrt
                (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1)))) ^ 2)) =
          ∑ a,
            (f ((E.chain a).label (Fin.castSucc j)) ((E.chain a).label (Fin.succ j)) *
              (E.chain a).amplitude j ^ 2) *
              (∑ b, Real.sqrt
                (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1)))) ^ 2) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ a,
          f ((E.chain a).label (Fin.castSucc j)) ((E.chain a).label (Fin.succ j)) *
            (E.chain a).amplitude j ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [sum_sq_sqrt_weight_div_row θ hrow]
          ring
      _ = ∑ a, ∑ b, f a b * θ.weight a b := hdiag j f

/-- Appending a normalized step preserves every old junction moment and
creates the required square-root row/column moment at the new junction. -/
theorem extend_junctionMatches (θ : CouplingTable) {n : ℕ}
    (E : Ensemble θ (n + 1)) (hdiag : E.DiagonalMatches)
    (hjunc : E.JunctionMatches)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c) :
    (extend θ E).JunctionMatches := by
  classical
  intro i hi f
  by_cases hold : i + 1 < n + 1
  · have hi0 : i < n + 1 := by omega
    have hi1 : i + 1 < n + 1 := hold
    simp only [extend]
    have hcast0 : (⟨i, by omega⟩ : Fin (n + 2)) =
        (⟨i, hi0⟩ : Fin (n + 1)).castSucc := rfl
    have hcast1 : (⟨i + 1, hi⟩ : Fin (n + 2)) =
        (⟨i + 1, hi1⟩ : Fin (n + 1)).castSucc := rfl
    rw [hcast0, hcast1]
    simp only [Fin.snoc_castSucc]
    have hlabel : (⟨i + 1, by omega⟩ : Fin (n + 3)) =
        (⟨i + 1, by omega⟩ : Fin (n + 2)).castSucc := rfl
    rw [hlabel]
    simp only [Fin.snoc_castSucc]
    change (∑ x : E.Index × θ.Label,
      f ((E.chain x.1).label ⟨i + 1, by omega⟩) *
        (((E.chain x.1).amplitude ⟨i, by omega⟩ *
            Real.sqrt (θ.weight ((E.chain x.1).label (Fin.last (n + 1))) x.2 /
              θ.row ((E.chain x.1).label (Fin.last (n + 1))))) *
          ((E.chain x.1).amplitude ⟨i + 1, hold⟩ *
            Real.sqrt (θ.weight ((E.chain x.1).label (Fin.last (n + 1))) x.2 /
              θ.row ((E.chain x.1).label (Fin.last (n + 1))))))) = _
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b,
          f ((E.chain a).label ⟨i + 1, by omega⟩) *
            (((E.chain a).amplitude ⟨i, by omega⟩ *
                Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1))))) *
              ((E.chain a).amplitude ⟨i + 1, hold⟩ *
                Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1))))))) =
          ∑ a,
            (f ((E.chain a).label ⟨i + 1, by omega⟩) *
              ((E.chain a).amplitude ⟨i, by omega⟩ *
                (E.chain a).amplitude ⟨i + 1, hold⟩)) *
              (∑ b, Real.sqrt
                (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1)))) ^ 2) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ a, f ((E.chain a).label ⟨i + 1, by omega⟩) *
          ((E.chain a).amplitude ⟨i, by omega⟩ *
            (E.chain a).amplitude ⟨i + 1, hold⟩) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [sum_sq_sqrt_weight_div_row θ hrow]
          ring
      _ = ∑ c, f c * Real.sqrt (θ.row c * θ.column c) := hjunc i hold f
  · have hieq : i = n := by omega
    subst i
    simp only [extend]
    have hshared : (⟨n + 1, by omega⟩ : Fin (n + 3)) =
        (Fin.last (n + 1)).castSucc := rfl
    have hampold : (⟨n, by omega⟩ : Fin (n + 2)) =
        (Fin.last n).castSucc := rfl
    have hampnew : (⟨n + 1, hi⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
    rw [hshared, hampold, hampnew]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    change (∑ x : E.Index × θ.Label,
      f ((E.chain x.1).label (Fin.last (n + 1))) *
        (((E.chain x.1).amplitude (Fin.last n) *
            Real.sqrt (θ.weight ((E.chain x.1).label (Fin.last (n + 1))) x.2 /
              θ.row ((E.chain x.1).label (Fin.last (n + 1))))) *
          ((E.chain x.1).amplitude (Fin.last n) *
            Real.sqrt (θ.weight ((E.chain x.1).label (Fin.last (n + 1))) x.2 /
              θ.column ((E.chain x.1).label (Fin.last (n + 1))))))) = _
    rw [Fintype.sum_prod_type]
    let g : θ.Label → ℝ := fun c =>
      f c * (θ.row c / Real.sqrt (θ.row c * θ.column c))
    calc
      (∑ a, ∑ b,
          f ((E.chain a).label (Fin.last (n + 1))) *
            (((E.chain a).amplitude (Fin.last n) *
                Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.row ((E.chain a).label (Fin.last (n + 1))))) *
              ((E.chain a).amplitude (Fin.last n) *
                Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  θ.column ((E.chain a).label (Fin.last (n + 1))))))) =
          ∑ a, ∑ b,
            f ((E.chain a).label (Fin.last (n + 1))) *
              ((E.chain a).amplitude (Fin.last n) ^ 2 *
                (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                  Real.sqrt (θ.row ((E.chain a).label (Fin.last (n + 1))) *
                    θ.column ((E.chain a).label (Fin.last (n + 1)))))) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [show
              ((E.chain a).amplitude (Fin.last n) *
                  Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                    θ.row ((E.chain a).label (Fin.last (n + 1))))) *
                ((E.chain a).amplitude (Fin.last n) *
                  Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                    θ.column ((E.chain a).label (Fin.last (n + 1))))) =
                (E.chain a).amplitude (Fin.last n) ^ 2 *
                  (Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                    θ.row ((E.chain a).label (Fin.last (n + 1)))) *
                  Real.sqrt (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                    θ.column ((E.chain a).label (Fin.last (n + 1))))) by ring]
            rw [sqrt_transition_mul θ hrow hcolumn]
      _ =
          ∑ a, g ((E.chain a).label (Fin.last (n + 1))) *
            (E.chain a).amplitude (Fin.last n) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            dsimp [g]
            calc
              (∑ b, f ((E.chain a).label (Fin.last (n + 1))) *
                ((E.chain a).amplitude (Fin.last n) ^ 2 *
                  (θ.weight ((E.chain a).label (Fin.last (n + 1))) b /
                    Real.sqrt (θ.row ((E.chain a).label (Fin.last (n + 1))) *
                      θ.column ((E.chain a).label (Fin.last (n + 1))))))) =
                (f ((E.chain a).label (Fin.last (n + 1))) *
                  (E.chain a).amplitude (Fin.last n) ^ 2 /
                    Real.sqrt (θ.row ((E.chain a).label (Fin.last (n + 1))) *
                      θ.column ((E.chain a).label (Fin.last (n + 1))))) *
                  (∑ b, θ.weight ((E.chain a).label (Fin.last (n + 1))) b) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro b _
                    ring
              _ = _ := by
                change _ * θ.row _ = _
                ring
      _ = ∑ c, g c * θ.column c := terminal_moment θ E hdiag g
      _ = ∑ c, f c * Real.sqrt (θ.row c * θ.column c) := by
        apply Finset.sum_congr rfl
        intro c _
        dsimp [g]
        have hp : 0 < θ.row c * θ.column c := mul_pos (hrow c) (hcolumn c)
        have hs : Real.sqrt (θ.row c * θ.column c) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 hp)
        field_simp
        rw [Real.sq_sqrt (le_of_lt hp)]
        ring

/-- The recursively constructed ensemble at every positive length. -/
noncomputable def walkEnsemble (θ : CouplingTable) : (N : ℕ) → 0 < N → Ensemble θ N
  | 0, h => (Nat.not_lt_zero _ h).elim
  | 1, _ => one θ
  | n + 2, _ => extend θ (walkEnsemble θ (n + 1) (by omega))

theorem walkEnsemble_amplitudesNonnegative (θ : CouplingTable)
    (N : ℕ) (hN : 0 < N) :
    (walkEnsemble θ N hN).AmplitudesNonnegative := by
  induction N using Nat.twoStepInduction with
  | zero => omega
  | one => exact one_amplitudesNonnegative θ
  | more n ih0 ih1 =>
      simp only [walkEnsemble]
      exact extend_amplitudesNonnegative θ _ (ih1 (by omega))

theorem walkEnsemble_diagonalMatches (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c)
    (N : ℕ) (hN : 0 < N) :
    (walkEnsemble θ N hN).DiagonalMatches := by
  induction N using Nat.twoStepInduction with
  | zero => omega
  | one => exact one_diagonalMatches θ
  | more n ih0 ih1 =>
      simp only [walkEnsemble]
      exact extend_diagonalMatches θ _ (ih1 (by omega)) hrow hcolumn

theorem walkEnsemble_junctionMatches (θ : CouplingTable)
    (hrow : ∀ c, 0 < θ.row c) (hcolumn : ∀ c, 0 < θ.column c)
    (N : ℕ) (hN : 0 < N) :
    (walkEnsemble θ N hN).JunctionMatches := by
  induction N using Nat.twoStepInduction with
  | zero => omega
  | one => exact one_junctionMatches θ
  | more n ih0 ih1 =>
      simp only [walkEnsemble]
      exact extend_junctionMatches θ _
        (walkEnsemble_diagonalMatches θ hrow hcolumn _ (by omega))
        (ih1 (by omega)) hrow hcolumn

end Ensemble
end CouplingTable
end I3322
