import I3322.EqualityChain
import I3322.ChainStationarity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# From a finite equality spine to a two-sided equality chain

This file isolates the purely discrete construction used at the end of the
equality case.  A finite list of interior labels and positive edge ratios is
clamped at both ends.  A ratio greater than one on the left and a ratio less
than one on the right determine square-summable geometric amplitude tails.
-/

namespace I3322

namespace FiniteSpine

/-- Clamp a natural index to `0, ..., n`. -/
def clampIndex (n k : ℕ) : Fin (n + 1) :=
  ⟨min k n, Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

@[simp] theorem clampIndex_zero (n : ℕ) : clampIndex n 0 = 0 := by
  ext
  simp [clampIndex]

@[simp] theorem clampIndex_last (n : ℕ) : clampIndex n n = Fin.last n := by
  ext
  simp [clampIndex]

theorem clampIndex_eq_last_of_le {n k : ℕ} (h : n ≤ k) :
    clampIndex n k = Fin.last n := by
  ext
  simp [clampIndex, min_eq_right h]

theorem clampIndex_eq_mk_of_le {n k : ℕ} (h : k ≤ n) :
    clampIndex n k = ⟨k, Nat.lt_succ_iff.mpr h⟩ := by
  ext
  simp [clampIndex, min_eq_left h]

@[simp] theorem clampIndex_castSucc_val {n : ℕ} (j : Fin n) :
    clampIndex n j.1 = j.castSucc := by
  ext
  simp [clampIndex, min_eq_left (Nat.le_of_lt j.2)]

@[simp] theorem clampIndex_succ_val {n : ℕ} (j : Fin n) :
    clampIndex n (j.1 + 1) = j.succ := by
  ext
  simp [clampIndex, min_eq_left (Nat.succ_le_iff.mpr j.2)]

/-- The predecessor label at a clamped finite vertex. -/
def prevLabel (n : ℕ) (c : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  c (clampIndex n (j.1 - 1))

/-- The successor label at a clamped finite vertex. -/
def nextLabel (n : ℕ) (c : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  c (clampIndex n (j.1 + 1))

end FiniteSpine

namespace FiniteSpineWindow

/-- The two half-junction contributions from consecutive cells telescope to
the full interior junction sum and two half boundary junctions. -/
theorem sum_adjacent_halves (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (f j / 2 + f (j + 1) / 2)) =
      f 0 / 2 + (∑ j ∈ Finset.range n, f (j + 1)) + f (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

theorem sum_sub_sum_eq_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (a : ι)
    (hfg : ∀ j, j ≠ a → f j = g j) :
    (∑ j, f j) - ∑ j, g j = f a - g a := by
  classical
  have ha : a ∈ (Finset.univ : Finset ι) := Finset.mem_univ a
  have hrest : (∑ j ∈ (Finset.univ.erase a), f j) =
      ∑ j ∈ (Finset.univ.erase a), g j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hfg j (Finset.ne_of_mem_erase hj)
  rw [← Finset.sum_erase_add _ f ha, ← Finset.sum_erase_add _ g ha]
  rw [hrest]
  ring

theorem sum_sub_sum_eq_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hfg : ∀ j, j ≠ a → j ≠ b → f j = g j) :
    (∑ j, f j) - ∑ j, g j =
      (f a - g a) + (f b - g b) := by
  classical
  have ha : a ∈ (Finset.univ : Finset ι) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ.erase a : Finset ι) := by
    simp [hab.symm]
  have hrest :
      (∑ j ∈ ((Finset.univ.erase a).erase b), f j) =
        ∑ j ∈ ((Finset.univ.erase a).erase b), g j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hfg j (by
      have := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      exact this) (Finset.ne_of_mem_erase hj)
  rw [← Finset.sum_erase_add _ f ha, ← Finset.sum_erase_add _ g ha,
    ← Finset.sum_erase_add _ f hb, ← Finset.sum_erase_add _ g hb]
  rw [hrest]
  ring

/-- A finite open PV chain whose labels are real numbers directly. -/
structure OpenChain (N : ℕ) where
  label : Fin (N + 1) → ℝ
  label_mem : ∀ j, label j ∈ Set.Icc (-1 : ℝ) 1
  amplitude : Fin N → ℝ
  amplitude_nonneg : ∀ j, 0 ≤ amplitude j
  norm_pos : 0 < ∑ j, amplitude j ^ 2

noncomputable def OpenChain.normSq {N : ℕ} (q : OpenChain N) : ℝ :=
  ∑ j, q.amplitude j ^ 2

noncomputable def OpenChain.numerator {N : ℕ} (q : OpenChain N) : ℝ :=
  (∑ j : Fin N,
      d (q.label j.castSucc) (q.label j.succ) * q.amplitude j ^ 2) +
    ∑ j : Fin (N - 1),
      s (q.label ⟨j.1 + 1, by omega⟩) *
        q.amplitude ⟨j.1, by omega⟩ * q.amplitude ⟨j.1 + 1, by omega⟩

/-- Replace one interior label of an open chain. -/
noncomputable def OpenChain.replaceLabel {N : ℕ} (q : OpenChain N)
    (t : Fin (N + 1)) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    OpenChain N where
  label j := if j = t then x else q.label j
  label_mem j := by
    by_cases h : j = t
    · simp [h, hx]
    · simp [h, q.label_mem j]
  amplitude := q.amplitude
  amplitude_nonneg := q.amplitude_nonneg
  norm_pos := q.norm_pos

@[simp] theorem OpenChain.replaceLabel_label_same {N : ℕ} (q : OpenChain N)
    (t : Fin (N + 1)) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (q.replaceLabel t x hx).label t = x := by
  simp [OpenChain.replaceLabel]

theorem OpenChain.replaceLabel_label_of_ne {N : ℕ} (q : OpenChain N)
    (t j : Fin (N + 1)) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hjt : j ≠ t) :
    (q.replaceLabel t x hx).label j = q.label j := by
  simp [OpenChain.replaceLabel, hjt]

/-- The three open-chain numerator terms affected by replacing an interior
label. -/
noncomputable def OpenChain.localObjective {N : ℕ} (q : OpenChain N)
    (t : Fin (N + 1)) (ht0 : 0 < t.1) (htN : t.1 < N) (x : ℝ) : ℝ :=
  d (q.label ⟨t.1 - 1, by omega⟩) x *
      q.amplitude ⟨t.1 - 1, by omega⟩ ^ 2 +
    d x (q.label ⟨t.1 + 1, by omega⟩) *
      q.amplitude ⟨t.1, by omega⟩ ^ 2 +
    s x * q.amplitude ⟨t.1 - 1, by omega⟩ *
      q.amplitude ⟨t.1, by omega⟩

/-- Replacing one interior label changes exactly its two diagonal cells and
their shared junction. -/
theorem OpenChain.replaceLabel_numerator_sub {N : ℕ} (q : OpenChain N)
    (t : Fin (N + 1)) (ht0 : 0 < t.1) (htN : t.1 < N)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (q.replaceLabel t x hx).numerator - q.numerator =
      q.localObjective t ht0 htN x -
        q.localObjective t ht0 htN (q.label t) := by
  classical
  let a : Fin N := ⟨t.1 - 1, by omega⟩
  let b : Fin N := ⟨t.1, htN⟩
  let u : Fin (N - 1) := ⟨t.1 - 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  let newDiag : Fin N → ℝ := fun j =>
    d ((q.replaceLabel t x hx).label j.castSucc)
        ((q.replaceLabel t x hx).label j.succ) * q.amplitude j ^ 2
  let oldDiag : Fin N → ℝ := fun j =>
    d (q.label j.castSucc) (q.label j.succ) * q.amplitude j ^ 2
  have hdiag : (∑ j, newDiag j) - ∑ j, oldDiag j =
      (newDiag a - oldDiag a) + (newDiag b - oldDiag b) := by
    apply sum_sub_sum_eq_two newDiag oldDiag a b hab
    intro j hja hjb
    have hjleft : j.castSucc ≠ t := by
      intro h
      apply hjb
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [b] at hv ⊢
      exact hv
    have hjright : j.succ ≠ t := by
      intro h
      apply hja
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [a] at hv ⊢
      omega
    simp [newDiag, oldDiag, OpenChain.replaceLabel, hjleft, hjright]
  let newJunction : Fin (N - 1) → ℝ := fun j =>
    s ((q.replaceLabel t x hx).label ⟨j.1 + 1, by omega⟩) *
      q.amplitude ⟨j.1, by omega⟩ * q.amplitude ⟨j.1 + 1, by omega⟩
  let oldJunction : Fin (N - 1) → ℝ := fun j =>
    s (q.label ⟨j.1 + 1, by omega⟩) *
      q.amplitude ⟨j.1, by omega⟩ * q.amplitude ⟨j.1 + 1, by omega⟩
  have hjunction : (∑ j, newJunction j) - ∑ j, oldJunction j =
      newJunction u - oldJunction u := by
    apply sum_sub_sum_eq_single newJunction oldJunction u
    intro j hju
    have hjlabel : (⟨j.1 + 1, by omega⟩ : Fin (N + 1)) ≠ t := by
      intro h
      apply hju
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [u] at hv ⊢
      omega
    simp [newJunction, oldJunction, OpenChain.replaceLabel, hjlabel]
  have hleftNot : (⟨t.1 - 1, by omega⟩ : Fin (N + 1)) ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    change t.1 - 1 = t.1 at hv
    omega
  have hmiddle : (⟨1 + (t.1 - 1), by omega⟩ : Fin (N + 1)) = t := by
    apply Fin.ext
    change 1 + (t.1 - 1) = t.1
    omega
  have hrightNot : (⟨1 + t.1, by omega⟩ : Fin (N + 1)) ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + t.1 = t.1 at hv
    omega
  have hmiddleAmp : (⟨1 + (t.1 - 1), by omega⟩ : Fin N) = b := by
    apply Fin.ext
    change 1 + (t.1 - 1) = t.1
    omega
  have haCastNe : a.castSucc ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [a] at hv
    omega
  have haSucc : a.succ = t := by
    apply Fin.ext
    dsimp [a]
    omega
  have hbCast : b.castSucc = t := by
    apply Fin.ext
    rfl
  have hbSuccNe : b.succ ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [b] at hv
    omega
  have huLabel : (⟨u.1 + 1, by omega⟩ : Fin (N + 1)) = t := by
    apply Fin.ext
    dsimp [u]
    omega
  have huAmpLeft : (⟨u.1, by omega⟩ : Fin N) = a := by
    apply Fin.ext
    rfl
  have huSucc_lt : u.1 + 1 < N := by
    dsimp [u]
    omega
  have huAmpRight : (⟨u.1 + 1, huSucc_lt⟩ : Fin N) = b := by
    apply Fin.ext
    change (t.1 - 1) + 1 = t.1
    omega
  have hreplaceLeft :
      (q.replaceLabel t x hx).label (⟨t.1 - 1, by omega⟩ : Fin (N + 1)) =
        q.label ⟨t.1 - 1, by omega⟩ :=
    q.replaceLabel_label_of_ne t _ x hx hleftNot
  have hreplaceRight :
      (q.replaceLabel t x hx).label (⟨1 + t.1, by omega⟩ : Fin (N + 1)) =
        q.label ⟨1 + t.1, by omega⟩ :=
    q.replaceLabel_label_of_ne t _ x hx hrightNot
  have hrightNot' : (⟨t.1 + 1, by omega⟩ : Fin (N + 1)) ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    change t.1 + 1 = t.1 at hv
    omega
  have hreplaceRight' :
      (q.replaceLabel t x hx).label (⟨t.1 + 1, by omega⟩ : Fin (N + 1)) =
        q.label ⟨t.1 + 1, by omega⟩ :=
    q.replaceLabel_label_of_ne t _ x hx hrightNot'
  unfold OpenChain.numerator
  change ((∑ j, newDiag j) + ∑ j, newJunction j) -
      ((∑ j, oldDiag j) + ∑ j, oldJunction j) = _
  rw [show (∑ j, newDiag j) + ∑ j, newJunction j -
        ((∑ j, oldDiag j) + ∑ j, oldJunction j) =
      ((∑ j, newDiag j) - ∑ j, oldDiag j) +
        ((∑ j, newJunction j) - ∑ j, oldJunction j) by ring,
    hdiag, hjunction]
  simp [newDiag, oldDiag, newJunction, oldJunction, a, b, u,
    OpenChain.localObjective, haCastNe, haSucc, hbCast, hbSuccNe,
    huLabel, huAmpLeft, huAmpRight, hleftNot, hmiddle, hrightNot,
    hmiddleAmp, hreplaceLeft]
  rw [hreplaceRight']
  ring

def natExtend {α : Type} {n : ℕ} (v : Fin n → α) (fallback : α)
    (i : ℕ) : α :=
  if h : i < n then v ⟨i, h⟩ else fallback

@[simp] theorem natExtend_apply_fin {α : Type} {n : ℕ} (v : Fin n → α)
    (fallback : α) (i : Fin n) : natExtend v fallback i = v i := by
  simp [natExtend, i.isLt]

noncomputable def OpenChain.paddedLabels {N : ℕ} (q : OpenChain N) :
    Fin (N + 3) → ℝ :=
  Fin.cons 1 (Fin.snoc q.label (-1))

noncomputable def OpenChain.paddedAmplitudes {N : ℕ} (q : OpenChain N) :
    Fin (N + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc q.amplitude 0)

theorem OpenChain.sum_paddedAmplitudes_sq {N : ℕ} (q : OpenChain N) :
    (∑ j, q.paddedAmplitudes j ^ 2) = ∑ j, q.amplitude j ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [paddedAmplitudes, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  norm_num

@[simp] theorem OpenChain.natPaddedAmplitude_zero {N : ℕ} (q : OpenChain N) :
    natExtend q.paddedAmplitudes 0 0 = 0 := by
  simp [natExtend, paddedAmplitudes]

@[simp] theorem OpenChain.natPaddedAmplitude_succ {N : ℕ} (q : OpenChain N)
    (j : Fin N) :
    natExtend q.paddedAmplitudes 0 (j.1 + 1) = q.amplitude j := by
  rw [natExtend]
  simp only [dif_pos (by omega : j.1 + 1 < N + 2)]
  change q.paddedAmplitudes j.castSucc.succ = q.amplitude j
  simp [paddedAmplitudes]

@[simp] theorem OpenChain.natPaddedAmplitude_last {N : ℕ} (q : OpenChain N) :
    natExtend q.paddedAmplitudes 0 (N + 1) = 0 := by
  rw [natExtend]
  simp only [dif_pos (by omega : N + 1 < N + 2)]
  change q.paddedAmplitudes (Fin.last (N + 1)) = 0
  simp [paddedAmplitudes]

@[simp] theorem OpenChain.natPaddedLabel_succ {N : ℕ} (q : OpenChain N)
    (j : Fin (N + 1)) :
    natExtend q.paddedLabels 0 (j.1 + 1) = q.label j := by
  rw [natExtend]
  simp only [dif_pos (by omega : j.1 + 1 < N + 3)]
  change q.paddedLabels j.castSucc.succ = q.label j
  simp [paddedLabels]

/-- Pad an open real-labelled chain by the required endpoint labels and zero
amplitudes. -/
noncomputable def OpenChain.toPV {N : ℕ} (q : OpenChain N) : PVChain where
  n := N + 2
  n_pos := by omega
  label := natExtend q.paddedLabels 0
  amplitude := natExtend q.paddedAmplitudes 0
  label_mem := by
    intro i hi
    have hi' : i < N + 3 := by omega
    rw [natExtend]
    simp only [dif_pos hi']
    let k : Fin (N + 3) := ⟨i, hi'⟩
    change q.paddedLabels k ∈ Set.Icc (-1 : ℝ) 1
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [paddedLabels]
    · refine Fin.lastCases ?_ (fun m => ?_) j
      · simp [paddedLabels]
      · simpa [paddedLabels] using q.label_mem m
  leftEndpoint := by simp [natExtend, paddedLabels]
  rightEndpoint := by
    rw [natExtend]
    simp only [dif_pos (by omega : N + 2 < N + 3)]
    change q.paddedLabels (Fin.last (N + 2)) = -1
    simp [paddedLabels]
  amplitude_nonneg := by
    intro i hi
    rw [natExtend]
    simp only [dif_pos hi]
    let k : Fin (N + 2) := ⟨i, hi⟩
    change 0 ≤ q.paddedAmplitudes k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [paddedAmplitudes]
    · refine Fin.lastCases ?_ (fun m => ?_) j
      · simp [paddedAmplitudes]
      · simpa [paddedAmplitudes] using q.amplitude_nonneg m
  normSq_pos := by
    rw [Finset.sum_range]
    simp only [natExtend_apply_fin]
    change 0 < ∑ j, q.paddedAmplitudes j ^ 2
    rw [q.sum_paddedAmplitudes_sq]
    exact q.norm_pos

theorem OpenChain.toPV_normSq {N : ℕ} (q : OpenChain N) :
    q.toPV.normSq = q.normSq := by
  rw [PVChain.normSq_eq_fin_sum]
  simp only [toPV, natExtend_apply_fin]
  change (∑ j, q.paddedAmplitudes j ^ 2) = ∑ j, q.amplitude j ^ 2
  exact q.sum_paddedAmplitudes_sq

theorem OpenChain.toPV_numerator {N : ℕ} (q : OpenChain N) :
    q.toPV.numerator = q.numerator := by
  cases N with
  | zero =>
      have h := q.norm_pos
      simp at h
  | succ n =>
      rw [PVChain.numerator_eq_fin_sums]
      simp only [toPV]
      unfold OpenChain.numerator
      let L : ℕ → ℝ := natExtend q.paddedLabels 0
      let A : ℕ → ℝ := natExtend q.paddedAmplitudes 0
      have hdiag :
          (∑ x : Fin (n + 3), d (L x) (L (x + 1)) * A x ^ 2) =
            ∑ j : Fin (n + 1),
              d (q.label j.castSucc) (q.label j.succ) *
                q.amplitude j ^ 2 := by
        rw [Fin.sum_univ_succ]
        have hA0 : A 0 = 0 := q.natPaddedAmplitude_zero
        have hA0' : A (↑(0 : Fin (n + 3))) = 0 := by simpa using hA0
        rw [hA0']
        norm_num
        rw [Fin.sum_univ_castSucc]
        have hAend : A ((Fin.last (n + 1) : ℕ) + 1) = 0 := by
          simpa [A] using q.natPaddedAmplitude_last
        rw [hAend]
        ring_nf
        apply Finset.sum_congr rfl
        intro j _
        have hA : A (1 + (j.castSucc : ℕ)) = q.amplitude j := by
          simpa [A, Nat.add_comm] using q.natPaddedAmplitude_succ j
        have hL : L (1 + (j.castSucc : ℕ)) = q.label j.castSucc := by
          simpa [L, Nat.add_comm] using q.natPaddedLabel_succ j.castSucc
        have hL' : L (2 + (j.castSucc : ℕ)) = q.label j.succ := by
          simpa [L, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            q.natPaddedLabel_succ j.succ
        rw [hA, hL, hL']
      have hjunc :
          (∑ x : Fin (n + 2), s (L (x + 1)) * A x * A (x + 1)) =
            ∑ j : Fin n,
              s (q.label ⟨j + 1, by omega⟩) *
                q.amplitude ⟨j, by omega⟩ *
                  q.amplitude ⟨j + 1, by omega⟩ := by
        rw [Fin.sum_univ_succ]
        have hA0 : A 0 = 0 := q.natPaddedAmplitude_zero
        have hA0' : A (↑(0 : Fin (n + 2))) = 0 := by simpa using hA0
        rw [hA0']
        ring_nf
        rw [Fin.sum_univ_castSucc]
        have hAend : A (1 + ((Fin.last n).succ : ℕ)) = 0 := by
          simpa [A, Nat.add_comm] using q.natPaddedAmplitude_last
        rw [hAend]
        simp only [mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        have hA : A j.castSucc.succ = q.amplitude j.castSucc := by
          simpa [A] using q.natPaddedAmplitude_succ j.castSucc
        have hA' : A (1 + (j.castSucc.succ : ℕ)) = q.amplitude j.succ := by
          simpa [A, Nat.add_comm] using q.natPaddedAmplitude_succ j.succ
        have hL : L (1 + (j.castSucc.succ : ℕ)) = q.label j.succ.castSucc := by
          simpa [L, Nat.add_comm] using q.natPaddedLabel_succ j.succ.castSucc
        rw [hA, hA', hL]
        have hidx0 : j.castSucc = (⟨j, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        have hidx1 : j.succ = (⟨1 + (j : ℕ), by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          change (j : ℕ) + 1 = 1 + (j : ℕ)
          omega
        have hlidx : j.succ.castSucc =
            (⟨1 + (j : ℕ), by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          change (j : ℕ) + 1 = 1 + (j : ℕ)
          omega
        rw [hidx0, hlidx, hidx1]
      change
        (∑ x : Fin (n + 3), d (L x) (L (x + 1)) * A x ^ 2) +
          (∑ x : Fin (n + 2), s (L (x + 1)) * A x * A (x + 1)) = _
      rw [hdiag, hjunc]
      rfl

/-- Every real-labelled open chain is bounded by `betaPV` after endpoint-zero
padding. -/
theorem OpenChain.numerator_le_beta_mul_norm {N : ℕ} (q : OpenChain N) :
    q.numerator ≤ betaPV * q.normSq := by
  have h := pvValue_le_betaPV q.toPV
  rw [PVChain.value, q.toPV_numerator, q.toPV_normSq] at h
  exact (div_le_iff₀ q.norm_pos).mp h

end FiniteSpineWindow

/-- Raw finite-spine data.  This contains no value or stationarity conclusion,
so equality extraction can construct its clamped sequences and amplitudes
before proving the equality equations. -/
structure FiniteSpineCore where
  n : ℕ
  n_pos : 0 < n
  label : Fin (n + 1) → ℝ
  ratio : Fin (n + 1) → ℝ
  label_mem_Icc : ∀ j, label j ∈ Set.Icc (-1 : ℝ) 1
  ratio_pos : ∀ j, 0 < ratio j
  left_ratio_gt_one : 1 < ratio 0
  right_ratio_lt_one : ratio (Fin.last n) < 1

/-- A finite spine satisfying the exact value recurrence.  No stationarity
equation is included: those equations are derived from finite PV bounds below. -/
structure ValueSpine extends FiniteSpineCore where
  label_mem_Ioo : ∀ j, label j ∈ Set.Ioo (-1 : ℝ) 1
  left_value :
    betaPV = d (label 0) (label 0) +
      s (label 0) / (2 * ratio 0) + s (label 0) / 2 * ratio 0
  edge_value : ∀ j : Fin n,
    betaPV = d (label j.castSucc) (label j.succ) +
      s (label j.castSucc) / (2 * ratio j.castSucc) +
      s (label j.succ) / 2 * ratio j.succ
  right_value :
    betaPV = d (label (Fin.last n)) (label (Fin.last n)) +
      s (label (Fin.last n)) / (2 * ratio (Fin.last n)) +
      s (label (Fin.last n)) / 2 * ratio (Fin.last n)

/-- Finite equality data after stationarity has been derived at the clamped
finite vertices and the two constant tails. -/
structure FiniteSpine extends ValueSpine where
  stationarity : ∀ j : Fin (n + 1),
    0 = FiniteSpine.prevLabel n label j - 1 / 2 +
      (FiniteSpine.nextLabel n label j + 1 / 2) * ratio j ^ 2 -
      label j / s (label j) * ratio j
  left_stationarity :
    0 = label 0 - 1 / 2 + (label 0 + 1 / 2) * ratio 0 ^ 2 -
      label 0 / s (label 0) * ratio 0
  right_stationarity :
    0 = label (Fin.last n) - 1 / 2 +
      (label (Fin.last n) + 1 / 2) * ratio (Fin.last n) ^ 2 -
      label (Fin.last n) / s (label (Fin.last n)) * ratio (Fin.last n)

namespace FiniteSpineCore

/-- The finite ratio sequence, clamped on the right. -/
def natRatio (F : FiniteSpineCore) (k : ℕ) : ℝ :=
  F.ratio (FiniteSpine.clampIndex F.n k)

/-- Product of the first `k` clamped ratios. -/
def prefixAmplitude (F : FiniteSpineCore) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, F.natRatio j

/-- The bi-infinite label sequence obtained by clamping the finite spine. -/
def clampedLabel (F : FiniteSpineCore) : ℤ → ℝ
  | .ofNat k => F.label (FiniteSpine.clampIndex F.n k)
  | .negSucc _ => F.label 0

/-- The bi-infinite ratio sequence obtained by clamping the finite spine. -/
def clampedRatio (F : FiniteSpineCore) : ℤ → ℝ
  | .ofNat k => F.natRatio k
  | .negSucc _ => F.ratio 0

/-- Positive amplitudes determined by the clamped ratios.  The left branch is
written with ordinary natural powers of the inverse, avoiding integer-power
normalization in the subsequent summability proof. -/
noncomputable def clampedAmplitude (F : FiniteSpineCore) : ℤ → ℝ
  | .ofNat k => F.prefixAmplitude k
  | .negSucc k => (F.ratio 0)⁻¹ ^ (k + 1)

theorem natRatio_pos (F : FiniteSpineCore) (k : ℕ) : 0 < F.natRatio k :=
  F.ratio_pos _

theorem prefixAmplitude_pos (F : FiniteSpineCore) (k : ℕ) :
    0 < F.prefixAmplitude k := by
  unfold prefixAmplitude
  apply Finset.prod_pos
  intro j hj
  exact F.natRatio_pos j

theorem prefixAmplitude_succ (F : FiniteSpineCore) (k : ℕ) :
    F.prefixAmplitude (k + 1) = F.prefixAmplitude k * F.natRatio k := by
  simpa [prefixAmplitude] using Finset.prod_range_succ F.natRatio k

theorem natRatio_eq_last_of_le (F : FiniteSpineCore) {k : ℕ}
    (h : F.n ≤ k) :
    F.natRatio k = F.ratio (Fin.last F.n) := by
  rw [natRatio, FiniteSpine.clampIndex_eq_last_of_le h]

/-- Beyond the last finite vertex, the prefix product is an exact geometric
tail with ratio `F.ratio (Fin.last F.n)`. -/
theorem prefixAmplitude_add_length (F : FiniteSpineCore) (k : ℕ) :
    F.prefixAmplitude (F.n + k) =
      F.prefixAmplitude F.n * F.ratio (Fin.last F.n) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, F.prefixAmplitude_succ, ih,
        F.natRatio_eq_last_of_le (Nat.le_add_right F.n k), pow_succ]
      ring

theorem clampedLabel_mem_Icc (F : FiniteSpineCore) (i : ℤ) :
    F.clampedLabel i ∈ Set.Icc (-1 : ℝ) 1 := by
  cases i <;> exact F.label_mem_Icc _

theorem clampedRatio_pos (F : FiniteSpineCore) (i : ℤ) :
    0 < F.clampedRatio i := by
  cases i <;> exact F.ratio_pos _

theorem clampedAmplitude_pos (F : FiniteSpineCore) (i : ℤ) :
    0 < F.clampedAmplitude i := by
  cases i with
  | ofNat k => exact F.prefixAmplitude_pos k
  | negSucc k =>
      exact pow_pos (inv_pos.mpr (F.ratio_pos 0)) _

/-- The explicit amplitudes have exactly the prescribed adjacent ratios. -/
theorem clampedRatio_eq_amplitude_div (F : FiniteSpineCore) (i : ℤ) :
    F.clampedRatio i = F.clampedAmplitude (i + 1) / F.clampedAmplitude i := by
  have hr0 : F.ratio 0 ≠ 0 := ne_of_gt (F.ratio_pos 0)
  cases i with
  | ofNat k =>
      rw [show (Int.ofNat k : ℤ) + 1 = Int.ofNat (k + 1) by simp]
      change F.natRatio k = F.prefixAmplitude (k + 1) / F.prefixAmplitude k
      rw [F.prefixAmplitude_succ]
      field_simp [ne_of_gt (F.prefixAmplitude_pos k)]
  | negSucc k =>
      cases k with
      | zero =>
          change F.ratio 0 = F.prefixAmplitude 0 / ((F.ratio 0)⁻¹ ^ 1)
          simp [prefixAmplitude, hr0]
      | succ k =>
          rw [show (Int.negSucc (k + 1) : ℤ) + 1 = Int.negSucc k by omega]
          change F.ratio 0 =
            ((F.ratio 0)⁻¹ ^ (k + 1)) /
              ((F.ratio 0)⁻¹ ^ (k + 2))
          have hden : (F.ratio 0)⁻¹ ^ (k + 2) =
              (F.ratio 0)⁻¹ ^ (k + 1) * (F.ratio 0)⁻¹ := by
            rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          rw [hden]
          rw [div_mul_cancel_left₀
            (pow_ne_zero _ (inv_ne_zero hr0))]
          simp

/-- The nonnegative half of the explicit amplitude sequence is summable. -/
theorem summable_clampedAmplitude_sq_nonnegative (F : FiniteSpineCore) :
    Summable (fun k : ℕ => F.clampedAmplitude (Int.ofNat k) ^ 2) := by
  let q : ℝ := F.ratio (Fin.last F.n) ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q < 1 := by
    dsimp [q]
    have hp := F.ratio_pos (Fin.last F.n)
    have hl := F.right_ratio_lt_one
    nlinarith
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hq0 hq1
  have hscaled : Summable (fun k : ℕ =>
      F.prefixAmplitude F.n ^ 2 * q ^ k) :=
    hgeom.mul_left _
  have hshift : Summable (fun k : ℕ =>
      F.clampedAmplitude (Int.ofNat (k + F.n)) ^ 2) := by
    refine hscaled.congr ?_
    intro k
    change F.prefixAmplitude F.n ^ 2 * q ^ k =
      F.prefixAmplitude (k + F.n) ^ 2
    rw [Nat.add_comm, F.prefixAmplitude_add_length]
    rw [mul_pow]
    congr 1
    dsimp [q]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  exact (summable_nat_add_iff F.n).mp hshift

/-- The negative half of the explicit amplitude sequence is summable. -/
theorem summable_clampedAmplitude_sq_negative (F : FiniteSpineCore) :
    Summable (fun k : ℕ =>
      F.clampedAmplitude (-(Int.ofNat k + 1)) ^ 2) := by
  let q : ℝ := (F.ratio 0)⁻¹ ^ 2
  have hinv0 : 0 ≤ (F.ratio 0)⁻¹ :=
    (inv_pos.mpr (F.ratio_pos 0)).le
  have hinv1 : (F.ratio 0)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ F.left_ratio_gt_one
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hq0 hq1
  have hshift : Summable (fun k : ℕ => q ^ (k + 1)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hgeom
  refine hshift.congr ?_
  intro k
  rw [show -(Int.ofNat k + 1) = Int.negSucc k by
    simp [Int.negSucc_eq, Int.ofNat_eq_natCast]]
  change q ^ (k + 1) = ((F.ratio 0)⁻¹ ^ (k + 1)) ^ 2
  dsimp [q]
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

/-- Both geometric tails and the finite middle are square-summable. -/
theorem clampedAmplitude_squareSummable (F : FiniteSpineCore) :
    Summable (fun i : ℤ => F.clampedAmplitude i ^ 2) := by
  exact Summable.of_nat_of_neg_add_one
    F.summable_clampedAmplitude_sq_nonnegative
    F.summable_clampedAmplitude_sq_negative

end FiniteSpineCore

namespace ValueSpine

abbrev clampedLabel (V : ValueSpine) : ℤ → ℝ :=
  V.toFiniteSpineCore.clampedLabel

abbrev clampedRatio (V : ValueSpine) : ℤ → ℝ :=
  V.toFiniteSpineCore.clampedRatio

noncomputable abbrev clampedAmplitude (V : ValueSpine) : ℤ → ℝ :=
  V.toFiniteSpineCore.clampedAmplitude

theorem clampedLabel_mem_Ioo (V : ValueSpine) (i : ℤ) :
    V.clampedLabel i ∈ Set.Ioo (-1 : ℝ) 1 := by
  cases i <;> exact V.label_mem_Ioo _

/-- The value recurrence holds at every integer vertex using only
`ValueSpine` data. -/
theorem clamped_ratio_recurrence (V : ValueSpine) (i : ℤ) :
    betaPV = d (V.clampedLabel (i - 1)) (V.clampedLabel i) +
      s (V.clampedLabel (i - 1)) / (2 * V.clampedRatio (i - 1)) +
      s (V.clampedLabel i) / 2 * V.clampedRatio i := by
  cases i with
  | negSucc k =>
      simpa [clampedLabel, clampedRatio, FiniteSpineCore.clampedLabel,
        FiniteSpineCore.clampedRatio] using V.left_value
  | ofNat k =>
      cases k with
      | zero =>
          rw [show (Int.ofNat 0 : ℤ) - 1 = Int.negSucc 0 by decide]
          simpa [clampedLabel, clampedRatio, FiniteSpineCore.clampedLabel,
            FiniteSpineCore.clampedRatio, FiniteSpineCore.natRatio,
            Int.ofNat_eq_natCast] using V.left_value
      | succ k =>
          by_cases hk : k < V.n
          · let j : Fin V.n := ⟨k, hk⟩
            have h := V.edge_value j
            have hk_le : k ≤ V.n := Nat.le_of_lt hk
            have hks_le : k + 1 ≤ V.n := Nat.succ_le_iff.mpr hk
            simpa [clampedLabel, clampedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio, j,
              FiniteSpine.clampIndex_eq_mk_of_le hk_le,
              FiniteSpine.clampIndex_eq_mk_of_le hks_le] using h
          · have hnk : V.n ≤ k := Nat.le_of_not_gt hk
            have hnks : V.n ≤ k + 1 := hnk.trans (Nat.le_succ k)
            simpa [clampedLabel, clampedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio,
              FiniteSpine.clampIndex_eq_last_of_le hnk,
              FiniteSpine.clampIndex_eq_last_of_le hnks] using V.right_value

/-- The value recurrence multiplied by the squared amplitude.  Adjacent-ratio
definitions turn its two half-junction terms into ordinary products. -/
theorem weighted_value_recurrence (V : ValueSpine) (i : ℤ) :
    betaPV * V.clampedAmplitude i ^ 2 =
      d (V.clampedLabel (i - 1)) (V.clampedLabel i) *
          V.clampedAmplitude i ^ 2 +
        s (V.clampedLabel (i - 1)) / 2 *
          V.clampedAmplitude (i - 1) * V.clampedAmplitude i +
        s (V.clampedLabel i) / 2 *
          V.clampedAmplitude i * V.clampedAmplitude (i + 1) := by
  have hvalue := V.clamped_ratio_recurrence i
  have hrprev := V.toFiniteSpineCore.clampedRatio_eq_amplitude_div (i - 1)
  have hri := V.toFiniteSpineCore.clampedRatio_eq_amplitude_div i
  have hrprev' : V.clampedRatio (i - 1) =
      V.clampedAmplitude i / V.clampedAmplitude (i - 1) := by
    convert hrprev using 1 <;> ring
  have hprev_ne : V.clampedAmplitude (i - 1) ≠ 0 :=
    ne_of_gt (V.toFiniteSpineCore.clampedAmplitude_pos (i - 1))
  have hi_ne : V.clampedAmplitude i ≠ 0 :=
    ne_of_gt (V.toFiniteSpineCore.clampedAmplitude_pos i)
  rw [hrprev'] at hvalue
  have hrightRatio :
      s (V.clampedLabel i) / 2 * V.clampedRatio i =
        s (V.clampedLabel i) / 2 *
          (V.clampedAmplitude (i + 1) / V.clampedAmplitude i) := by
    exact congrArg (fun z => s (V.clampedLabel i) / 2 * z) hri
  rw [hrightRatio] at hvalue
  have hleft :
      s (V.clampedLabel (i - 1)) /
            (2 * (V.clampedAmplitude i / V.clampedAmplitude (i - 1))) *
          V.clampedAmplitude i ^ 2 =
        s (V.clampedLabel (i - 1)) / 2 *
          V.clampedAmplitude (i - 1) * V.clampedAmplitude i := by
    field_simp [hprev_ne, hi_ne]
  have hright :
      s (V.clampedLabel i) / 2 *
            (V.clampedAmplitude (i + 1) / V.clampedAmplitude i) *
          V.clampedAmplitude i ^ 2 =
        s (V.clampedLabel i) / 2 *
          V.clampedAmplitude i * V.clampedAmplitude (i + 1) := by
    field_simp [hi_ne]
  calc
    betaPV * V.clampedAmplitude i ^ 2 =
        (d (V.clampedLabel (i - 1)) (V.clampedLabel i) +
          s (V.clampedLabel (i - 1)) /
            (2 * (V.clampedAmplitude i / V.clampedAmplitude (i - 1))) +
          s (V.clampedLabel i) / 2 *
            (V.clampedAmplitude (i + 1) / V.clampedAmplitude i)) *
          V.clampedAmplitude i ^ 2 := by rw [hvalue]
    _ = _ := by rw [add_mul, add_mul, hleft, hright]

end ValueSpine

namespace FiniteSpine

/-- The clamped label sequence of the underlying raw core. -/
abbrev extendedLabel (F : FiniteSpine) : ℤ → ℝ :=
  F.toFiniteSpineCore.clampedLabel

/-- The clamped ratio sequence of the underlying raw core. -/
abbrev extendedRatio (F : FiniteSpine) : ℤ → ℝ :=
  F.toFiniteSpineCore.clampedRatio

/-- The square-summable amplitude sequence of the underlying raw core. -/
noncomputable abbrev extendedAmplitude (F : FiniteSpine) : ℤ → ℝ :=
  F.toFiniteSpineCore.clampedAmplitude

theorem extendedLabel_mem_Ioo (F : FiniteSpine) (i : ℤ) :
    F.extendedLabel i ∈ Set.Ioo (-1 : ℝ) 1 := by
  cases i <;> exact F.label_mem_Ioo _

/-- The value recurrence holds at every integer vertex of the clamped spine. -/
theorem extended_ratio_recurrence (F : FiniteSpine) (i : ℤ) :
    betaPV = d (F.extendedLabel (i - 1)) (F.extendedLabel i) +
      s (F.extendedLabel (i - 1)) / (2 * F.extendedRatio (i - 1)) +
      s (F.extendedLabel i) / 2 * F.extendedRatio i := by
  cases i with
  | negSucc k =>
      simpa [extendedLabel, extendedRatio, FiniteSpineCore.clampedLabel,
        FiniteSpineCore.clampedRatio] using F.left_value
  | ofNat k =>
      cases k with
      | zero =>
          rw [show (Int.ofNat 0 : ℤ) - 1 = Int.negSucc 0 by decide]
          simpa [extendedLabel, extendedRatio, FiniteSpineCore.clampedLabel,
            FiniteSpineCore.clampedRatio, FiniteSpineCore.natRatio,
            Int.ofNat_eq_natCast] using
            F.left_value
      | succ k =>
          by_cases hk : k < F.n
          · let j : Fin F.n := ⟨k, hk⟩
            have h := F.edge_value j
            have hk_le : k ≤ F.n := Nat.le_of_lt hk
            have hks_le : k + 1 ≤ F.n := Nat.succ_le_iff.mpr hk
            simpa [extendedLabel, extendedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio, j,
              clampIndex_eq_mk_of_le hk_le,
              clampIndex_eq_mk_of_le hks_le] using h
          · have hnk : F.n ≤ k := Nat.le_of_not_gt hk
            have hnks : F.n ≤ k + 1 := hnk.trans (Nat.le_succ k)
            simpa [extendedLabel, extendedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio,
              clampIndex_eq_last_of_le hnk,
              clampIndex_eq_last_of_le hnks] using F.right_value

/-- The finite and constant-tail stationarity hypotheses cover every integer
vertex of the clamped spine. -/
theorem extended_label_recurrence (F : FiniteSpine) (i : ℤ) :
    0 = F.extendedLabel (i - 1) - 1 / 2 +
      (F.extendedLabel (i + 1) + 1 / 2) * F.extendedRatio i ^ 2 -
      F.extendedLabel i / s (F.extendedLabel i) * F.extendedRatio i := by
  cases i with
  | negSucc k =>
      cases k with
      | zero =>
          rw [show (Int.negSucc 0 : ℤ) - 1 = Int.negSucc 1 by decide,
            show (Int.negSucc 0 : ℤ) + 1 = Int.ofNat 0 by decide]
          simpa [extendedLabel, extendedRatio, FiniteSpineCore.clampedLabel,
            FiniteSpineCore.clampedRatio] using F.left_stationarity
      | succ k =>
          rw [show (Int.negSucc (k + 1) : ℤ) - 1 = Int.negSucc (k + 2) by
              omega,
            show (Int.negSucc (k + 1) : ℤ) + 1 = Int.negSucc k by omega]
          simpa [extendedLabel, extendedRatio, FiniteSpineCore.clampedLabel,
            FiniteSpineCore.clampedRatio] using F.left_stationarity
  | ofNat k =>
      by_cases hk : k ≤ F.n
      · have h := F.stationarity (clampIndex F.n k)
        cases k with
        | zero =>
            rw [show (Int.ofNat 0 : ℤ) - 1 = Int.negSucc 0 by decide]
            simpa [extendedLabel, extendedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio, prevLabel, nextLabel,
              clampIndex, Int.ofNat_eq_natCast] using h
        | succ k =>
            rw [show (Int.ofNat (k + 1) : ℤ) - 1 = Int.ofNat k by
              simp [Int.ofNat_eq_natCast],
              show (Int.ofNat (k + 1) : ℤ) + 1 = Int.ofNat (k + 2) by
                simp [Int.ofNat_eq_natCast]
                omega]
            simpa [extendedLabel, extendedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio, prevLabel, nextLabel,
              clampIndex, min_eq_left hk, Int.ofNat_eq_natCast] using h
      · have hnk : F.n < k := Nat.lt_of_not_ge hk
        cases k with
        | zero => omega
        | succ k =>
            have hnprev : F.n ≤ k := by omega
            have hncur : F.n ≤ k + 1 := hnprev.trans (Nat.le_succ k)
            have hnnext : F.n ≤ k + 2 := hncur.trans (Nat.le_succ (k + 1))
            rw [show (Int.ofNat (k + 1) : ℤ) - 1 = Int.ofNat k by
              simp [Int.ofNat_eq_natCast],
              show (Int.ofNat (k + 1) : ℤ) + 1 = Int.ofNat (k + 2) by
                simp [Int.ofNat_eq_natCast]
                omega]
            simpa [extendedLabel, extendedRatio,
              FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
              FiniteSpineCore.natRatio,
              clampIndex_eq_last_of_le hnprev,
              clampIndex_eq_last_of_le hncur,
              clampIndex_eq_last_of_le hnnext] using F.right_stationarity

/-- Package the clamped finite spine as the exact `EqualityChain` consumed by
the already formalized propagation contradiction. -/
noncomputable def toEqualityChain (F : FiniteSpine) : EqualityChain where
  label := F.extendedLabel
  amplitude := F.extendedAmplitude
  ratio := F.extendedRatio
  label_mem := F.extendedLabel_mem_Ioo
  amplitude_pos := F.toFiniteSpineCore.clampedAmplitude_pos
  ratio_def := F.toFiniteSpineCore.clampedRatio_eq_amplitude_div
  ratio_pos := F.toFiniteSpineCore.clampedRatio_pos
  ratio_recurrence := F.extended_ratio_recurrence
  label_recurrence := F.extended_label_recurrence
  squareSummable := F.toFiniteSpineCore.clampedAmplitude_squareSummable
  tailLabel := F.label 0
  tailRatio := F.ratio 0
  tailRatio_gt_one := F.left_ratio_gt_one
  tailEnd := -1
  left_tail_label := by
    intro i hi
    cases i with
    | ofNat k =>
        have hk0 : (0 : ℤ) ≤ Int.ofNat k := by
          simpa [Int.ofNat_eq_natCast] using Int.ofNat_zero_le k
        omega
    | negSucc k => rfl
  left_tail_ratio := by
    intro i hi
    cases i with
    | ofNat k =>
        have hk0 : (0 : ℤ) ≤ Int.ofNat k := by
          simpa [Int.ofNat_eq_natCast] using Int.ofNat_zero_le k
        omega
    | negSucc k => rfl

/-- Terminal finite-spine interface: the supplied finite equations construct a
two-sided equality chain. -/
theorem nonempty_equalityChain (F : FiniteSpine) : Nonempty EqualityChain :=
  ⟨F.toEqualityChain⟩

end FiniteSpine

namespace ValueSpine

open scoped BigOperators

/-! ### Centered finite windows

The following definitions cut a finite open PV chain out of the explicit
square-summable amplitude sequence.  The extra amplitude on either side of
the distinguished label keeps all three terms of its one-label objective
strictly inside the window. -/

/-- A centered window has `2 * N + 3` amplitudes. -/
def windowEdgeCount (N : ℕ) : ℕ := 2 * N + 3

/-- The integer index of the first amplitude in the centered window. -/
def windowLeftIndex (i : ℤ) (N : ℕ) : ℤ := i - (N : ℤ) - 1

/-- The finite label position occupied by the distinguished label `c i`. -/
def windowTarget (N : ℕ) : Fin (windowEdgeCount N + 1) :=
  ⟨N + 2, by simp [windowEdgeCount]; omega⟩

/-- The centered open chain cut out of a value spine. -/
noncomputable def centeredWindow (V : ValueSpine) (i : ℤ) (N : ℕ) :
    FiniteSpineWindow.OpenChain (windowEdgeCount N) where
  label j := V.clampedLabel (windowLeftIndex i N + (j.1 : ℤ) - 1)
  label_mem j := by
    exact ⟨le_of_lt (V.clampedLabel_mem_Ioo _).1,
      le_of_lt (V.clampedLabel_mem_Ioo _).2⟩
  amplitude j := V.clampedAmplitude (windowLeftIndex i N + (j.1 : ℤ))
  amplitude_nonneg j :=
    le_of_lt (V.toFiniteSpineCore.clampedAmplitude_pos _)
  norm_pos := by
    let j : Fin (windowEdgeCount N) := ⟨0, by simp [windowEdgeCount]⟩
    have hj :
        0 < V.clampedAmplitude (windowLeftIndex i N + (j.1 : ℤ)) ^ 2 :=
      sq_pos_of_pos (V.toFiniteSpineCore.clampedAmplitude_pos _)
    exact lt_of_lt_of_le hj
      (Finset.single_le_sum
        (fun k _ => sq_nonneg
          (V.clampedAmplitude (windowLeftIndex i N + (k.1 : ℤ))))
        (Finset.mem_univ j))

theorem windowTarget_pos (N : ℕ) : 0 < (windowTarget N).1 := by
  simp [windowTarget]

theorem windowTarget_lt (N : ℕ) :
    (windowTarget N).1 < windowEdgeCount N := by
  simp [windowTarget, windowEdgeCount]
  omega

/-- A junction term, indexed by its shared integer label. -/
noncomputable def junction (V : ValueSpine) (k : ℤ) : ℝ :=
  s (V.clampedLabel k) * V.clampedAmplitude k * V.clampedAmplitude (k + 1)

/-- The exact two-boundary defect of a centered window. -/
noncomputable def windowDefect (V : ValueSpine) (i : ℤ) (N : ℕ) : ℝ :=
  (V.junction (i - (N : ℤ) - 2) +
    V.junction (i + (N : ℤ) + 1)) / 2

@[simp] theorem centeredWindow_target_label
    (V : ValueSpine) (i : ℤ) (N : ℕ) :
    (V.centeredWindow i N).label (windowTarget N) = V.clampedLabel i := by
  simp [centeredWindow, windowTarget, windowLeftIndex]
  push_cast
  congr 1
  ring

/-- The finite and integer-indexed local objectives agree exactly. -/
theorem centeredWindow_localObjective
    (V : ValueSpine) (i : ℤ) (N : ℕ) (x : ℝ) :
    (V.centeredWindow i N).localObjective (windowTarget N)
        (windowTarget_pos N) (windowTarget_lt N) x =
      ChainStationarity.localLabelObjective
        V.clampedLabel V.clampedAmplitude i x := by
  unfold FiniteSpineWindow.OpenChain.localObjective
  unfold ChainStationarity.localLabelObjective
  simp [centeredWindow, windowTarget, windowLeftIndex]
  push_cast
  congr 1 <;> ring

theorem centeredWindow_normSq (V : ValueSpine) (i : ℤ) (N : ℕ) :
    (V.centeredWindow i N).normSq =
      ∑ j : Fin (windowEdgeCount N),
        V.clampedAmplitude (windowLeftIndex i N + (j.1 : ℤ)) ^ 2 := by
  rfl

theorem centeredWindow_numerator (V : ValueSpine) (i : ℤ) (N : ℕ) :
    (V.centeredWindow i N).numerator =
      (∑ j : Fin (windowEdgeCount N),
        d (V.clampedLabel (windowLeftIndex i N + (j.1 : ℤ) - 1))
            (V.clampedLabel (windowLeftIndex i N + (j.1 : ℤ))) *
          V.clampedAmplitude (windowLeftIndex i N + (j.1 : ℤ)) ^ 2) +
        ∑ j : Fin (windowEdgeCount N - 1),
          V.junction (windowLeftIndex i N + (j.1 : ℤ)) := by
  unfold FiniteSpineWindow.OpenChain.numerator centeredWindow junction
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 3 <;> simp <;> push_cast <;> ring
  · apply Finset.sum_congr rfl
    intro j _
    simp
    push_cast
    congr 1 <;> ring

/-- Summing the exact value recurrence over a centered window leaves only
the two half-junctions at its boundary. -/
theorem centeredWindow_defect_eq (V : ValueSpine) (i : ℤ) (N : ℕ) :
    betaPV * (V.centeredWindow i N).normSq -
        (V.centeredWindow i N).numerator = V.windowDefect i N := by
  let m : ℕ := windowEdgeCount N
  let L : ℤ := windowLeftIndex i N
  let diag : ℕ → ℝ := fun j =>
    d (V.clampedLabel (L + (j : ℤ) - 1))
        (V.clampedLabel (L + (j : ℤ))) *
      V.clampedAmplitude (L + (j : ℤ)) ^ 2
  let halfs : ℕ → ℝ := fun j =>
    V.junction (L + (j : ℤ) - 1) / 2 +
      V.junction (L + (j : ℤ)) / 2
  let shiftedJunction : ℕ → ℝ := fun j =>
    V.junction (L - 1 + (j : ℤ))
  have hpoint (j : ℕ) :
      betaPV * V.clampedAmplitude (L + (j : ℤ)) ^ 2 =
        diag j + halfs j := by
    have h := V.weighted_value_recurrence (L + (j : ℤ))
    dsimp [diag, halfs]
    unfold junction
    convert h using 1 <;> ring
  have hsum :
      (∑ j ∈ Finset.range m,
          betaPV * V.clampedAmplitude (L + (j : ℤ)) ^ 2) =
        (∑ j ∈ Finset.range m, diag j) +
          ∑ j ∈ Finset.range m, halfs j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpoint j)
  have hm : 0 < m := by simp [m, windowEdgeCount]
  have hmPred : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt hm))
  have hhalf_point (j : ℕ) :
      halfs j = shiftedJunction j / 2 + shiftedJunction (j + 1) / 2 := by
    dsimp [halfs, shiftedJunction]
    congr 1 <;> ring
  have hhalfs' :
      (∑ j ∈ Finset.range m, halfs j) =
        shiftedJunction 0 / 2 +
          (∑ j ∈ Finset.range (m - 1), shiftedJunction (j + 1)) +
            shiftedJunction m / 2 := by
    calc
      (∑ j ∈ Finset.range m, halfs j) =
          ∑ j ∈ Finset.range m,
            (shiftedJunction j / 2 + shiftedJunction (j + 1) / 2) := by
              apply Finset.sum_congr rfl
              intro j _
              exact hhalf_point j
      _ = _ := by
        simpa only [hmPred] using
          (FiniteSpineWindow.sum_adjacent_halves shiftedJunction (m - 1))
  rw [centeredWindow_normSq, centeredWindow_numerator]
  rw [Fin.sum_univ_eq_sum_range
      (fun j => V.clampedAmplitude (windowLeftIndex i N + (j : ℤ)) ^ 2)
      (windowEdgeCount N),
    Fin.sum_univ_eq_sum_range
      (fun j =>
        d (V.clampedLabel (windowLeftIndex i N + (j : ℤ) - 1))
            (V.clampedLabel (windowLeftIndex i N + (j : ℤ))) *
          V.clampedAmplitude (windowLeftIndex i N + (j : ℤ)) ^ 2)
      (windowEdgeCount N),
    Fin.sum_univ_eq_sum_range
      (fun j => V.junction (windowLeftIndex i N + (j : ℤ)))
      (windowEdgeCount N - 1)]
  change betaPV *
      (∑ j ∈ Finset.range m,
        V.clampedAmplitude (L + (j : ℤ)) ^ 2) -
      ((∑ j ∈ Finset.range m, diag j) +
        ∑ j ∈ Finset.range (m - 1),
          V.junction (L + (j : ℤ))) = V.windowDefect i N
  rw [Finset.mul_sum, hsum, hhalfs']
  have hinter (j : ℕ) :
      shiftedJunction (j + 1) = V.junction (L + (j : ℤ)) := by
    dsimp [shiftedJunction]
    congr 1
    push_cast
    ring
  have hinterSum :
      (∑ j ∈ Finset.range (m - 1), shiftedJunction (j + 1)) =
        ∑ j ∈ Finset.range (m - 1),
          V.junction (L + (j : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hinter j
  rw [hinterSum]
  dsimp [shiftedJunction, windowDefect, L, m, windowLeftIndex,
    windowEdgeCount]
  congr 1 <;> push_cast <;> ring

theorem junction_nonneg (V : ValueSpine) (k : ℤ) :
    0 ≤ V.junction k := by
  unfold junction
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _)
      (le_of_lt (V.toFiniteSpineCore.clampedAmplitude_pos k)))
    (le_of_lt (V.toFiniteSpineCore.clampedAmplitude_pos (k + 1)))

theorem s_clampedLabel_le_one (V : ValueSpine) (k : ℤ) :
    s (V.clampedLabel k) ≤ 1 := by
  unfold s
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg (V.clampedLabel k)]

/-- A junction is bounded by the arithmetic mean of the adjacent squared
amplitudes. -/
theorem junction_le_sq_mean (V : ValueSpine) (k : ℤ) :
    V.junction k ≤
      (V.clampedAmplitude k ^ 2 + V.clampedAmplitude (k + 1) ^ 2) / 2 := by
  have hs1 := V.s_clampedLabel_le_one k
  have ha := V.toFiniteSpineCore.clampedAmplitude_pos k
  have hb := V.toFiniteSpineCore.clampedAmplitude_pos (k + 1)
  unfold junction
  have hprod :
      0 ≤ V.clampedAmplitude k * V.clampedAmplitude (k + 1) :=
    mul_nonneg ha.le hb.le
  have hmul :
      s (V.clampedLabel k) * V.clampedAmplitude k *
          V.clampedAmplitude (k + 1) ≤
        V.clampedAmplitude k * V.clampedAmplitude (k + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hprod]
  nlinarith [sq_nonneg
    (V.clampedAmplitude k - V.clampedAmplitude (k + 1))]

/-- Junctions tend to zero along every injectively indexed subsequence. -/
theorem junction_tendsto_zero_comp (V : ValueSpine) (k : ℕ → ℤ)
    (hk : Function.Injective k) :
    Filter.Tendsto (fun N => V.junction (k N)) Filter.atTop (nhds 0) := by
  have hk1 : Function.Injective (fun N => k N + 1) := by
    intro a b h
    apply hk
    exact add_right_cancel h
  have hsq0 : Filter.Tendsto
      (fun N => V.clampedAmplitude (k N) ^ 2) Filter.atTop (nhds 0) :=
    (V.toFiniteSpineCore.clampedAmplitude_squareSummable.comp_injective
      hk).tendsto_atTop_zero
  have hsq1 : Filter.Tendsto
      (fun N => V.clampedAmplitude (k N + 1) ^ 2) Filter.atTop (nhds 0) :=
    (V.toFiniteSpineCore.clampedAmplitude_squareSummable.comp_injective
      hk1).tendsto_atTop_zero
  have hu : Filter.Tendsto
      (fun N => (V.clampedAmplitude (k N) ^ 2 +
        V.clampedAmplitude (k N + 1) ^ 2) / 2)
      Filter.atTop (nhds 0) := by
    convert (hsq0.add hsq1).div_const 2 using 1 <;> norm_num
  exact squeeze_zero
    (fun N => V.junction_nonneg (k N))
    (fun N => V.junction_le_sq_mean (k N)) hu

/-- Both boundary junctions of the centered window vanish. -/
theorem windowDefect_tendsto_zero (V : ValueSpine) (i : ℤ) :
    Filter.Tendsto (V.windowDefect i) Filter.atTop (nhds 0) := by
  have hleft : Function.Injective
      (fun N : ℕ => i - (N : ℤ) - 2) := by
    intro a b h
    push_cast at h
    omega
  have hright : Function.Injective
      (fun N : ℕ => i + (N : ℤ) + 1) := by
    intro a b h
    push_cast at h
    omega
  have hl := V.junction_tendsto_zero_comp
    (fun N : ℕ => i - (N : ℤ) - 2) hleft
  have hr := V.junction_tendsto_zero_comp
    (fun N : ℕ => i + (N : ℤ) + 1) hright
  unfold windowDefect
  convert (hl.add hr).div_const 2 using 1 <;> norm_num

/-- The exact centered-window deficit tends to zero. -/
theorem centeredWindow_defect_tendsto_zero (V : ValueSpine) (i : ℤ) :
    Filter.Tendsto
      (fun N => betaPV * (V.centeredWindow i N).normSq -
        (V.centeredWindow i N).numerator)
      Filter.atTop (nhds 0) := by
  simpa only [V.centeredWindow_defect_eq] using
    V.windowDefect_tendsto_zero i

/-- Replacing the distinguished label in any centered window is bounded by
the finite PV supremum.  The displayed correction is exactly the change of
the three local terms. -/
theorem centeredWindow_replacement_bound
    (V : ValueSpine) (i : ℤ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (N : ℕ) :
    (V.centeredWindow i N).numerator +
        (ChainStationarity.localLabelObjective
            V.clampedLabel V.clampedAmplitude i x -
          ChainStationarity.localLabelObjective
            V.clampedLabel V.clampedAmplitude i (V.clampedLabel i)) ≤
      betaPV * (V.centeredWindow i N).normSq := by
  let q := V.centeredWindow i N
  let t := windowTarget N
  let qx := q.replaceLabel t x hx
  have hchange := q.replaceLabel_numerator_sub t
    (windowTarget_pos N) (windowTarget_lt N) x hx
  have hbound := qx.numerator_le_beta_mul_norm
  have hnorm : qx.normSq = q.normSq := by
    rfl
  rw [hnorm] at hbound
  have hlocalx := V.centeredWindow_localObjective i N x
  have hlocal0 := V.centeredWindow_localObjective i N (V.clampedLabel i)
  have htarget := V.centeredWindow_target_label i N
  dsimp [q, t, qx] at hchange hbound ⊢
  rw [hlocalx, htarget, hlocal0] at hchange
  linarith

/-- Every clamped label satisfies the exact stationarity equation obtained by
differentiating only a finite, one-label objective after its boundary defect
has been sent to zero. -/
theorem clamped_label_stationarity (V : ValueSpine) (i : ℤ) :
    0 = V.clampedLabel (i - 1) - 1 / 2 +
      (V.clampedLabel (i + 1) + 1 / 2) * V.clampedRatio i ^ 2 -
      V.clampedLabel i / s (V.clampedLabel i) * V.clampedRatio i := by
  have h := ChainStationarity.label_stationarity_of_finite_windows
    V.clampedLabel V.clampedAmplitude i
    (V.clampedLabel_mem_Ioo i)
    (V.toFiniteSpineCore.clampedAmplitude_pos i)
    (fun N => (V.centeredWindow i N).numerator)
    (fun N => (V.centeredWindow i N).normSq)
    (V.centeredWindow_defect_tendsto_zero i)
    (fun x hx N => V.centeredWindow_replacement_bound i x hx N)
  rw [← V.toFiniteSpineCore.clampedRatio_eq_amplitude_div i] at h
  exact h

/-- Package stationarity at every clamped integer index into the finite
stationarity fields used by `FiniteSpine`. -/
noncomputable def toFiniteSpineOfStationarity (V : ValueSpine)
    (hstat : ∀ i : ℤ,
      0 = V.clampedLabel (i - 1) - 1 / 2 +
        (V.clampedLabel (i + 1) + 1 / 2) * V.clampedRatio i ^ 2 -
        V.clampedLabel i / s (V.clampedLabel i) * V.clampedRatio i) :
    FiniteSpine where
  toValueSpine := V
  stationarity := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · have h := hstat 0
      rw [show (0 : ℤ) - 1 = Int.negSucc 0 by decide] at h
      simpa [ValueSpine.clampedLabel, ValueSpine.clampedRatio,
        FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
        FiniteSpineCore.natRatio, FiniteSpine.prevLabel,
        FiniteSpine.nextLabel, FiniteSpine.clampIndex] using h
    · have h := hstat (Int.ofNat (k.1 + 1))
      rw [show (Int.ofNat (k.1 + 1) : ℤ) - 1 = Int.ofNat k.1 by
          simp [Int.ofNat_eq_natCast],
        show (Int.ofNat (k.1 + 1) : ℤ) + 1 = Int.ofNat (k.1 + 2) by
          simp [Int.ofNat_eq_natCast]
          omega] at h
      simpa [ValueSpine.clampedLabel, ValueSpine.clampedRatio,
        FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
        FiniteSpineCore.natRatio, FiniteSpine.prevLabel,
        FiniteSpine.nextLabel] using h
  left_stationarity := by
    have h := hstat (Int.negSucc 0)
    rw [show (Int.negSucc 0 : ℤ) - 1 = Int.negSucc 1 by decide,
      show (Int.negSucc 0 : ℤ) + 1 = 0 by decide] at h
    simpa [ValueSpine.clampedLabel, ValueSpine.clampedRatio,
      FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio] using h
  right_stationarity := by
    have h := hstat (Int.ofNat (V.n + 1))
    rw [show (Int.ofNat (V.n + 1) : ℤ) - 1 = Int.ofNat V.n by
        simp [Int.ofNat_eq_natCast],
      show (Int.ofNat (V.n + 1) : ℤ) + 1 = Int.ofNat (V.n + 2) by
        simp [Int.ofNat_eq_natCast]
        omega] at h
    simpa [ValueSpine.clampedLabel, ValueSpine.clampedRatio,
      FiniteSpineCore.clampedLabel, FiniteSpineCore.clampedRatio,
      FiniteSpineCore.natRatio,
      FiniteSpine.clampIndex_eq_last_of_le (Nat.le_succ V.n),
      FiniteSpine.clampIndex_eq_last_of_le (Nat.le_add_right V.n 2)] using h

/-- The canonical finite spine obtained from the value recurrences and finite
PV bounds. -/
noncomputable def toFiniteSpine (V : ValueSpine) : FiniteSpine :=
  V.toFiniteSpineOfStationarity V.clamped_label_stationarity

/-- Terminal generic bridge: exact value recurrences on a finite support
spine force a forbidden square-summable two-sided equality chain. -/
theorem nonempty_equalityChain (V : ValueSpine) : Nonempty EqualityChain :=
  V.toFiniteSpine.nonempty_equalityChain

end ValueSpine
end I3322
