import I3322.PV
import I3322.SchmidtStrategy
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional realization of every PV chain

This file implements the block projectors displayed in the manuscript and
evaluates their Born-rule `I3322` score.  To avoid a parity split, a
chain with `n` amplitudes is padded by zero amplitudes to dimension `2*n+1`.
The first `n` coordinates are unchanged, so the padding does not change the PV
numerator or norm.
-/

namespace I3322
namespace PVRealization

open scoped BigOperators ComplexConjugate

/-- Real `2 × 2` Pál--Vértesi block, embedded in complex matrices. -/
noncomputable def block (a b t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then (a : ℂ)
    else if i = 0 ∧ j = 1 then (t : ℂ)
    else if i = 1 ∧ j = 0 then (t : ℂ)
    else (b : ℂ)

@[simp] theorem block_apply_zero_zero (a b t : ℝ) : block a b t 0 0 = a := by
  simp [block]

@[simp] theorem block_apply_zero_one (a b t : ℝ) : block a b t 0 1 = t := by
  simp [block]

@[simp] theorem block_apply_one_zero (a b t : ℝ) : block a b t 1 0 = t := by
  simp [block]

@[simp] theorem block_apply_one_one (a b t : ℝ) : block a b t 1 1 = b := by
  simp [block]

theorem s_sq {c : ℝ} (hc : c ∈ Set.Icc (-1 : ℝ) 1) : s c ^ 2 = 1 - c ^ 2 := by
  rw [s, Real.sq_sqrt]
  nlinarith [hc.1, hc.2]

/-- `P_σ(c)`; `σ = -1` or `+1` chooses the off-diagonal sign. -/
noncomputable def pBlock (σ c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  block ((1 - c) / 2) ((1 + c) / 2) (σ * s c / 2)

/-- `Q_σ(c)`; its diagonal entries are swapped relative to `P_σ(c)`. -/
noncomputable def qBlock (σ c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  block ((1 + c) / 2) ((1 - c) / 2) (σ * s c / 2)

/-- The fixed rank-one block `Π₊`. -/
noncomputable def piPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  block (1 / 2) (1 / 2) (1 / 2)

theorem block_hermitian (a b t : ℝ) :
    (block a b t).conjTranspose = block a b t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem pBlock_idempotent {σ c : ℝ} (hσ : σ ^ 2 = 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    pBlock σ c * pBlock σ c = pBlock σ c := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, pBlock]
  all_goals apply Complex.ext <;> simp
  all_goals nlinarith [s_sq hc]

theorem qBlock_idempotent {σ c : ℝ} (hσ : σ ^ 2 = 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    qBlock σ c * qBlock σ c = qBlock σ c := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, qBlock]
  all_goals apply Complex.ext <;> simp
  all_goals nlinarith [s_sq hc]

theorem piPlus_idempotent : piPlus * piPlus = piPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, piPlus]

/-- A block-diagonal matrix on `Fin m × Fin 2`. -/
noncomputable def blockDiagonal {m : ℕ}
    (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ :=
  fun i j => if i.1 = j.1 then M i.1 i.2 j.2 else 0

theorem blockDiagonal_hermitian {m : ℕ}
    (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ k, (M k).conjTranspose = M k) :
    (blockDiagonal M).conjTranspose = blockDiagonal M := by
  ext i j
  by_cases hij : i.1 = j.1
  · simp only [Matrix.conjTranspose_apply, blockDiagonal, hij, if_pos,
      starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun (hM j.1) i.2) j.2
  · have hji : j.1 ≠ i.1 := Ne.symm hij
    simp [Matrix.conjTranspose_apply, blockDiagonal, hij, hji]

theorem blockDiagonal_idempotent {m : ℕ}
    (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ k, M k * M k = M k) :
    blockDiagonal M * blockDiagonal M = blockDiagonal M := by
  ext i j
  simp only [Matrix.mul_apply, blockDiagonal]
  rw [Fintype.sum_prod_type]
  by_cases hij : i.1 = j.1
  · rw [if_pos hij]
    rw [Finset.sum_eq_single i.1]
    · simpa [Matrix.mul_apply, hij] using
        congrFun (congrFun (hM i.1) i.2) j.2
    · intro b _ hbi
      simp [hbi, Ne.symm hbi]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.1 = k
    · have hkj : k ≠ j.1 := by simpa [← hik] using hij
      simp [hik, hkj]
    · simp [hik]

/-- Block-diagonal orthogonal projection. -/
noncomputable def blockDiagonalProjection {m : ℕ}
    (P : Fin m → OrthogonalProjection 2) :
    OrthogonalProjection (m * 2) := by
  let e : (Fin m × Fin 2) ≃ Fin (m * 2) := finProdFinEquiv
  let M : Matrix (Fin (m * 2)) (Fin (m * 2)) ℂ :=
    (Matrix.reindex e e) (blockDiagonal fun k => (P k).matrix)
  refine ⟨M, ?_, ?_⟩
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [M, Matrix.reindex_apply, Equiv.symm_apply_apply,
      Matrix.conjTranspose_apply]
    have h := congrFun (congrFun
      (blockDiagonal_hermitian (fun k => (P k).matrix) fun k => (P k).hermitian)
      i) j
    simpa [Matrix.conjTranspose_apply] using h
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [M, Matrix.mul_apply, Matrix.reindex_apply, Equiv.symm_apply_apply]
    rw [← e.sum_comp]
    simpa [Matrix.mul_apply] using congrFun (congrFun
      (blockDiagonal_idempotent (fun k => (P k).matrix) fun k => (P k).idempotent)
      i) j

/-- Reindexing a projection by a basis equivalence preserves both laws. -/
noncomputable def reindexProjection {m n : ℕ} (e : Fin m ≃ Fin n)
    (P : OrthogonalProjection m) : OrthogonalProjection n := by
  let M := (Matrix.reindex e e) P.matrix
  refine ⟨M, ?_, ?_⟩
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [M, Matrix.reindex_apply, Matrix.conjTranspose_apply]
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun P.hermitian i) j
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [M, Matrix.mul_apply, Matrix.reindex_apply]
    rw [← e.sum_comp]
    simpa [Matrix.mul_apply] using congrFun (congrFun P.idempotent i) j

/-- Orthogonal direct sum of two projections. -/
noncomputable def sumProjection {m n : ℕ}
    (P : OrthogonalProjection m) (Q : OrthogonalProjection n) :
    OrthogonalProjection (m + n) := by
  let E : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let D : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    Matrix.fromBlocks P.matrix 0 0 Q.matrix
  let M := (Matrix.reindex E E) D
  refine ⟨M, ?_, ?_⟩
  · ext i j
    obtain ⟨i, rfl⟩ := E.surjective i
    obtain ⟨j, rfl⟩ := E.surjective j
    simp only [M, Matrix.reindex_apply, Matrix.conjTranspose_apply]
    have hD : D.conjTranspose = D := by
      simp [D, Matrix.fromBlocks_conjTranspose, P.hermitian, Q.hermitian]
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hD i) j
  · ext i j
    obtain ⟨i, rfl⟩ := E.surjective i
    obtain ⟨j, rfl⟩ := E.surjective j
    simp only [M, Matrix.mul_apply, Matrix.reindex_apply]
    rw [← E.sum_comp]
    have hD : D * D = D := by
      simp [D, Matrix.fromBlocks_multiply, P.idempotent, Q.idempotent]
    simpa [Matrix.mul_apply] using congrFun (congrFun hD i) j

/-- The projector `P_σ(c)` as a packaged operator. -/
noncomputable def pProjection (σ c : ℝ) (hσ : σ ^ 2 = 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) : OrthogonalProjection 2 where
  matrix := pBlock σ c
  hermitian := block_hermitian _ _ _
  idempotent := pBlock_idempotent hσ hc

/-- The projector `Q_σ(c)` as a packaged operator. -/
noncomputable def qProjection (σ c : ℝ) (hσ : σ ^ 2 = 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) : OrthogonalProjection 2 where
  matrix := qBlock σ c
  hermitian := block_hermitian _ _ _
  idempotent := qBlock_idempotent hσ hc

/-- The packaged fixed rank-one projector `Π₊`. -/
noncomputable def piPlusProjection : OrthogonalProjection 2 where
  matrix := piPlus
  hermitian := block_hermitian _ _ _
  idempotent := piPlus_idempotent

/-- Dimension used for the uniformly odd zero padding. -/
def pvDim (p : PVChain) : ℕ := 1 + p.n * 2

theorem pvDim_pos (p : PVChain) : 0 < pvDim p := by
  simp [pvDim]

/-- The label sequence padded on the right by copies of the endpoint `-1`. -/
noncomputable def paddedLabel (p : PVChain) (i : ℕ) : ℝ :=
  if i ≤ p.n then p.label i else -1

/-- The amplitude sequence padded on the right by zeros. -/
noncomputable def paddedAmplitude (p : PVChain) (i : ℕ) : ℝ :=
  if i < p.n then p.amplitude i else 0

theorem paddedLabel_mem (p : PVChain) (i : ℕ) :
    paddedLabel p i ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases hi : i ≤ p.n
  · simpa [paddedLabel, hi] using p.label_mem i hi
  · simp [paddedLabel, hi]

@[simp] theorem paddedAmplitude_eq (p : PVChain) {i : ℕ} (hi : i < p.n) :
    paddedAmplitude p i = p.amplitude i := by simp [paddedAmplitude, hi]

@[simp] theorem paddedAmplitude_eq_zero (p : PVChain) {i : ℕ} (hi : p.n ≤ i) :
    paddedAmplitude p i = 0 := by simp [paddedAmplitude, Nat.not_lt.mpr hi]

/-- Alice's first/second block families, before adjoining the scalar block. -/
noncomputable def aliceBlocks (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Fin p.n → OrthogonalProjection 2 :=
  fun k => pProjection σ (paddedLabel p (2 * k.val + 2)) hσ
    (paddedLabel_mem p _)

/-- Bob's first/second block families, before adjoining the scalar block. -/
noncomputable def bobBlocks (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Fin p.n → OrthogonalProjection 2 :=
  fun k => qProjection σ (paddedLabel p (2 * k.val + 1)) hσ
    (paddedLabel_mem p _)

/-- Basis equivalence for Alice's pairing: scalar first, then `n` pairs. -/
def aliceEquiv (p : PVChain) : Fin (1 + p.n * 2) ≃ Fin (pvDim p) :=
  finCongr rfl

/-- Basis equivalence putting Bob's scalar block at the last coordinate. -/
def bobEquiv (p : PVChain) : Fin (p.n * 2 + 1) ≃ Fin (pvDim p) :=
  finCongr (by simp [pvDim, Nat.add_comm])

/-- Full coordinate map for Alice's scalar-plus-pairs decomposition. -/
def aliceFullEquiv (p : PVChain) :
    (Fin 1 ⊕ (Fin p.n × Fin 2)) ≃ Fin (pvDim p) :=
  ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv).trans
    (aliceEquiv p)

/-- Full coordinate map for Bob's pairs-plus-scalar decomposition. -/
def bobFullEquiv (p : PVChain) :
    ((Fin p.n × Fin 2) ⊕ Fin 1) ≃ Fin (pvDim p) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (bobEquiv p)

/-- Package a Hermitian idempotent matrix after a finite basis reindexing. -/
noncomputable def projectionFromEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) (M : Matrix ι ι ℂ)
    (hH : M.conjTranspose = M) (hI : M * M = M) :
    OrthogonalProjection n := by
  let N := (Matrix.reindex e e) M
  refine ⟨N, ?_, ?_⟩
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [N, Matrix.reindex_apply, Matrix.conjTranspose_apply]
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hH i) j
  · ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [N, Matrix.mul_apply, Matrix.reindex_apply]
    rw [← e.sum_comp]
    simpa [Matrix.mul_apply] using congrFun (congrFun hI i) j

noncomputable def aliceSource (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Matrix (Fin 1 ⊕ (Fin p.n × Fin 2)) (Fin 1 ⊕ (Fin p.n × Fin 2)) ℂ :=
  Matrix.fromBlocks 1 0 0
    (blockDiagonal fun k => (aliceBlocks p σ hσ k).matrix)

noncomputable def bobSource (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Matrix ((Fin p.n × Fin 2) ⊕ Fin 1) ((Fin p.n × Fin 2) ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks
    (blockDiagonal fun k => (bobBlocks p σ hσ k).matrix) 0 0 0

noncomputable def aliceThirdSource (p : PVChain) :
    Matrix ((Fin p.n × Fin 2) ⊕ Fin 1) ((Fin p.n × Fin 2) ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (blockDiagonal fun _ : Fin p.n => piPlus) 0 0 1

noncomputable def bobThirdSource (p : PVChain) :
    Matrix (Fin 1 ⊕ (Fin p.n × Fin 2)) (Fin 1 ⊕ (Fin p.n × Fin 2)) ℂ :=
  Matrix.fromBlocks 1 0 0 (blockDiagonal fun _ : Fin p.n => piPlus)

/-- Alice's outcome-`1` effect for measurement 1 or 2. -/
noncomputable def aliceEffect (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    OrthogonalProjection (pvDim p) := by
  apply projectionFromEquiv (aliceFullEquiv p) (aliceSource p σ hσ)
  · have hb := blockDiagonal_hermitian
      (fun k => (aliceBlocks p σ hσ k).matrix)
      (fun k => (aliceBlocks p σ hσ k).hermitian)
    simp [aliceSource, Matrix.fromBlocks_conjTranspose, hb]
  · have hb := blockDiagonal_idempotent
      (fun k => (aliceBlocks p σ hσ k).matrix)
      (fun k => (aliceBlocks p σ hσ k).idempotent)
    simp [aliceSource, Matrix.fromBlocks_multiply, hb]

/-- Bob's outcome-`1` effect for measurement 1 or 2. -/
noncomputable def bobEffect (p : PVChain) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    OrthogonalProjection (pvDim p) := by
  apply projectionFromEquiv (bobFullEquiv p) (bobSource p σ hσ)
  · have hb := blockDiagonal_hermitian
      (fun k => (bobBlocks p σ hσ k).matrix)
      (fun k => (bobBlocks p σ hσ k).hermitian)
    simp [bobSource, Matrix.fromBlocks_conjTranspose, hb]
  · have hb := blockDiagonal_idempotent
      (fun k => (bobBlocks p σ hσ k).matrix)
      (fun k => (bobBlocks p σ hσ k).idempotent)
    simp [bobSource, Matrix.fromBlocks_multiply, hb]

/-- Alice's third measurement: `Π₊` on Bob's pairs and `1` at the end. -/
noncomputable def aliceThird (p : PVChain) : OrthogonalProjection (pvDim p) :=
  projectionFromEquiv (bobFullEquiv p) (aliceThirdSource p)
    (by
      have hb := blockDiagonal_hermitian
        (fun _ : Fin p.n => piPlus) (fun _ => block_hermitian _ _ _)
      simp [aliceThirdSource, Matrix.fromBlocks_conjTranspose, hb])
    (by
      have hb := blockDiagonal_idempotent
        (fun _ : Fin p.n => piPlus) (fun _ => piPlus_idempotent)
      simp [aliceThirdSource, Matrix.fromBlocks_multiply, hb])

/-- Bob's third measurement: `1` first and `Π₊` on Alice's pairs. -/
noncomputable def bobThird (p : PVChain) : OrthogonalProjection (pvDim p) :=
  projectionFromEquiv (aliceFullEquiv p) (bobThirdSource p)
    (by
      have hb := blockDiagonal_hermitian
        (fun _ : Fin p.n => piPlus) (fun _ => block_hermitian _ _ _)
      simp [bobThirdSource, Matrix.fromBlocks_conjTranspose, hb])
    (by
      have hb := blockDiagonal_idempotent
        (fun _ : Fin p.n => piPlus) (fun _ => piPlus_idempotent)
      simp [bobThirdSource, Matrix.fromBlocks_multiply, hb])

@[simp] theorem aliceEffect_source_apply (p : PVChain) (σ : ℝ)
    (hσ : σ ^ 2 = 1) (i j : Fin 1 ⊕ (Fin p.n × Fin 2)) :
    (aliceEffect p σ hσ).matrix (aliceFullEquiv p i) (aliceFullEquiv p j) =
      aliceSource p σ hσ i j := by
  simp [aliceEffect, projectionFromEquiv, Matrix.reindex_apply]

@[simp] theorem bobEffect_source_apply (p : PVChain) (σ : ℝ)
    (hσ : σ ^ 2 = 1) (i j : (Fin p.n × Fin 2) ⊕ Fin 1) :
    (bobEffect p σ hσ).matrix (bobFullEquiv p i) (bobFullEquiv p j) =
      bobSource p σ hσ i j := by
  simp [bobEffect, projectionFromEquiv, Matrix.reindex_apply]

@[simp] theorem aliceThird_source_apply (p : PVChain)
    (i j : (Fin p.n × Fin 2) ⊕ Fin 1) :
    (aliceThird p).matrix (bobFullEquiv p i) (bobFullEquiv p j) =
      aliceThirdSource p i j := by
  simp [aliceThird, projectionFromEquiv, Matrix.reindex_apply]

@[simp] theorem bobThird_source_apply (p : PVChain)
    (i j : Fin 1 ⊕ (Fin p.n × Fin 2)) :
    (bobThird p).matrix (aliceFullEquiv p i) (aliceFullEquiv p j) =
      bobThirdSource p i j := by
  simp [bobThird, projectionFromEquiv, Matrix.reindex_apply]

@[simp] theorem aliceFullEquiv_scalar_val (p : PVChain) (i : Fin 1) :
    (aliceFullEquiv p (Sum.inl i)).val = 0 := by
  fin_cases i
  rfl

@[simp] theorem aliceFullEquiv_pair_val (p : PVChain)
    (k : Fin p.n) (a : Fin 2) :
    (aliceFullEquiv p (Sum.inr (k, a))).val = 1 + a.val + 2 * k.val := by
  simp [aliceFullEquiv, aliceEquiv, finProdFinEquiv]
  omega

@[simp] theorem bobFullEquiv_pair_val (p : PVChain)
    (k : Fin p.n) (a : Fin 2) :
    (bobFullEquiv p (Sum.inl (k, a))).val = a.val + 2 * k.val := by
  rfl

@[simp] theorem bobFullEquiv_scalar_val (p : PVChain) (i : Fin 1) :
    (bobFullEquiv p (Sum.inr i)).val = 2 * p.n := by
  fin_cases i
  change p.n * 2 = 2 * p.n
  omega

theorem bob_pair_one_eq_alice_pair_zero (p : PVChain) (k : Fin p.n) :
    bobFullEquiv p (Sum.inl (k, (1 : Fin 2))) =
      aliceFullEquiv p (Sum.inr (k, (0 : Fin 2))) := by
  apply Fin.ext
  simp

theorem bob_pair_zero_eq_alice_scalar (p : PVChain) (k : Fin p.n)
    (hk : k.val = 0) :
    bobFullEquiv p (Sum.inl (k, (0 : Fin 2))) =
      aliceFullEquiv p (Sum.inl (0 : Fin 1)) := by
  apply Fin.ext
  simp [hk]

theorem bob_pair_zero_eq_alice_pred (p : PVChain) (k : Fin p.n)
    (hk : k.val ≠ 0) :
    bobFullEquiv p (Sum.inl (k, (0 : Fin 2))) =
      aliceFullEquiv p
        (Sum.inr (⟨k.val - 1, by omega⟩, (1 : Fin 2))) := by
  apply Fin.ext
  simp
  omega

theorem bob_scalar_eq_alice_last (p : PVChain) (i : Fin 1) :
    bobFullEquiv p (Sum.inr i) =
      aliceFullEquiv p
        (Sum.inr (⟨p.n - 1, by have := p.n_pos; omega⟩, (1 : Fin 2))) := by
  apply Fin.ext
  simp
  have := p.n_pos
  omega

private theorem neg_one_sq : (-1 : ℝ) ^ 2 = 1 := by norm_num
private theorem one_sq : (1 : ℝ) ^ 2 = 1 := by norm_num

/-- The diagonal coefficient left after grouping the marginal and `1,2` terms. -/
noncomputable def diagonalKernel (p : PVChain) (i : Fin (pvDim p)) : ℂ :=
  -(aliceEffect p 1 one_sq).matrix i i
    -(bobEffect p (-1) neg_one_sq).matrix i i
    -2 * (bobEffect p 1 one_sq).matrix i i
    +((aliceEffect p (-1) neg_one_sq).matrix i i
        +(aliceEffect p 1 one_sq).matrix i i)
      *((bobEffect p (-1) neg_one_sq).matrix i i
        +(bobEffect p 1 one_sq).matrix i i)

theorem diagonalKernel_eq (p : PVChain) (i : Fin (pvDim p)) :
    diagonalKernel p i =
      (d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) : ℂ) := by
  obtain ⟨u, rfl⟩ := (bobFullEquiv p).surjective i
  rcases u with u | u
  · rcases u with ⟨k, a⟩
    by_cases ha : a.val = 0
    · have ha' : a = (0 : Fin 2) := Fin.ext ha
      subst a
      by_cases hk : k.val = 0
      · have he := bob_pair_zero_eq_alice_scalar p k hk
        simp only [diagonalKernel]
        simp only [bobEffect_source_apply]
        rw [he]
        simp only [aliceEffect_source_apply]
        simp [aliceSource, bobSource, aliceBlocks, bobBlocks, pProjection,
          qProjection, blockDiagonal, pBlock, qBlock, paddedLabel, hk,
          PVChain.leftEndpoint]
        have hn := p.n_pos
        simp [hn, Nat.succ_le_iff, d]
        push_cast
        ring
      · have he := bob_pair_zero_eq_alice_pred p k hk
        simp only [diagonalKernel]
        simp only [bobEffect_source_apply]
        rw [he]
        simp only [aliceEffect_source_apply]
        simp [aliceSource, bobSource, aliceBlocks, bobBlocks, pProjection,
          qProjection, blockDiagonal, pBlock, qBlock]
        have h1 : 2 * (k.val - 1) + 2 = 2 * k.val := by omega
        have h2 : 2 + 2 * (k.val - 1) = 2 * k.val := by omega
        have h3 : 2 + 2 * (k.val - 1) + 1 = 2 * k.val + 1 := by omega
        simp only [h1, h2, h3]
        simp [d]
        push_cast
        ring
    · have ha1 : a.val = 1 := by omega
      have ha' : a = (1 : Fin 2) := Fin.ext ha1
      subst a
      have he := bob_pair_one_eq_alice_pair_zero p k
      simp only [diagonalKernel]
      simp only [bobEffect_source_apply]
      rw [he]
      simp only [aliceEffect_source_apply]
      simp [aliceSource, bobSource, aliceBlocks, bobBlocks, pProjection,
        qProjection, blockDiagonal, pBlock, qBlock]
      have h1 : 1 + 2 * k.val = 2 * k.val + 1 := by omega
      have h2 : 1 + 2 * k.val + 1 = 2 * k.val + 2 := by omega
      simp only [h1, h2]
      simp [d]
      push_cast
      ring
  · have he := bob_scalar_eq_alice_last p u
    simp only [diagonalKernel]
    simp only [bobEffect_source_apply]
    rw [he]
    simp only [aliceEffect_source_apply]
    simp [aliceSource, bobSource, aliceBlocks, bobBlocks, pProjection,
      qProjection, blockDiagonal, pBlock, qBlock, paddedLabel,
      PVChain.rightEndpoint]
    have hn := p.n_pos
    split_ifs <;> try omega
    simp [d]

/-- Off-diagonal kernel on Alice's complementary (even-label) pairs. -/
noncomputable def evenKernel (p : PVChain) (i k : Fin (pvDim p)) : ℂ :=
  ((aliceEffect p 1 one_sq).matrix i k
      -(aliceEffect p (-1) neg_one_sq).matrix i k) *
    (bobThird p).matrix i k

/-- Off-diagonal kernel on Bob's complementary (odd-label) pairs. -/
noncomputable def oddKernel (p : PVChain) (i k : Fin (pvDim p)) : ℂ :=
  (aliceThird p).matrix i k *
    ((bobEffect p 1 one_sq).matrix i k
      -(bobEffect p (-1) neg_one_sq).matrix i k)

theorem evenKernel_sum (p : PVChain) :
    (∑ i : Fin (pvDim p), ∑ k : Fin (pvDim p),
      (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
        evenKernel p i k) =
      ∑ q : Fin p.n,
        (s (paddedLabel p (2 * q.val + 2)) : ℂ) *
          (paddedAmplitude p (2 * q.val + 1) : ℂ) *
          (paddedAmplitude p (2 * q.val + 2) : ℂ) := by
  classical
  let e := aliceFullEquiv p
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp]
  dsimp only [e]
  simp only [evenKernel, aliceEffect_source_apply, bobThird_source_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    aliceSource, bobThirdSource, aliceBlocks, pProjection, blockDiagonal,
    pBlock, piPlus]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem oddKernel_sum (p : PVChain) :
    (∑ i : Fin (pvDim p), ∑ k : Fin (pvDim p),
      (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
        oddKernel p i k) =
      ∑ q : Fin p.n,
        (s (paddedLabel p (2 * q.val + 1)) : ℂ) *
          (paddedAmplitude p (2 * q.val) : ℂ) *
          (paddedAmplitude p (2 * q.val + 1) : ℂ) := by
  classical
  let e := bobFullEquiv p
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp]
  dsimp only [e]
  simp only [oddKernel, aliceThird_source_apply, bobEffect_source_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    aliceThirdSource, bobSource, bobBlocks, qProjection, blockDiagonal,
    qBlock, piPlus]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem paddedAmplitude_normSq (p : PVChain) :
    (∑ i : Fin (pvDim p), (paddedAmplitude p i.val) ^ 2) = p.normSq := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (paddedAmplitude p k) ^ 2) (pvDim p)]
  have hdim : pvDim p = p.n + (p.n + 1) := by
    simp [pvDim]
    omega
  rw [hdim, Finset.sum_range_add]
  simp only [paddedAmplitude]
  have htail : (∑ x ∈ Finset.range (p.n + 1),
      (if p.n + x < p.n then p.amplitude (p.n + x) else 0) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp
  rw [htail, add_zero]
  unfold PVChain.normSq
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (Finset.mem_range.mp hx)]

/-- The padded Schmidt-diagonal state coefficient matrix. -/
noncomputable def pvState (p : PVChain) :
    Matrix (Fin (pvDim p)) (Fin (pvDim p)) ℂ :=
  fun i j => if i = j then (paddedAmplitude p i.val : ℂ) else 0

theorem pvState_normSq (p : PVChain) :
    (∑ i : Fin (pvDim p), ∑ j : Fin (pvDim p),
      Complex.normSq (pvState p i j)) = p.normSq := by
  classical
  have hrow : ∀ i : Fin (pvDim p),
      (∑ j : Fin (pvDim p), Complex.normSq (pvState p i j)) =
        (paddedAmplitude p i.val) ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [pvState, Complex.normSq_ofReal, pow_two]
    · intro j _ hji
      simp [pvState, Ne.symm hji]
    · simp
  simp_rw [hrow]
  exact paddedAmplitude_normSq p

/-- The explicit PV data in canonical Schmidt form. -/
noncomputable def schmidtStrategy (p : PVChain) : SchmidtStrategy where
  dim := pvDim p
  dim_pos := pvDim_pos p
  amplitude := fun i => paddedAmplitude p i.val
  amplitude_nonneg := by
    intro i
    by_cases hi : i.val < p.n
    · simpa [paddedAmplitude, hi] using p.amplitude_nonneg i.val hi
    · simp [paddedAmplitude, hi]
  normSq_pos := by
    rw [paddedAmplitude_normSq]
    exact p.normSq_pos'
  alice := fun x =>
    if x = 0 then aliceEffect p (-1) (by norm_num)
    else if x = 1 then aliceEffect p 1 (by norm_num)
    else aliceThird p
  bob := fun y =>
    if y = 0 then bobEffect p (-1) (by norm_num)
    else if y = 1 then bobEffect p 1 (by norm_num)
    else bobThird p

/-- The explicit finite-dimensional Pál--Vértesi strategy. -/
noncomputable def strategy (p : PVChain) : QuantumStrategy :=
  (schmidtStrategy p).toQuantumStrategy

@[simp] theorem strategy_alice_zero (p : PVChain) :
    (strategy p).alice 0 = aliceEffect p (-1) (by norm_num) := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

@[simp] theorem strategy_alice_one (p : PVChain) :
    (strategy p).alice 1 = aliceEffect p 1 (by norm_num) := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

@[simp] theorem strategy_alice_two (p : PVChain) :
    (strategy p).alice 2 = aliceThird p := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

@[simp] theorem strategy_bob_zero (p : PVChain) :
    (strategy p).bob 0 = bobEffect p (-1) (by norm_num) := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

@[simp] theorem strategy_bob_one (p : PVChain) :
    (strategy p).bob 1 = bobEffect p 1 (by norm_num) := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

@[simp] theorem strategy_bob_two (p : PVChain) :
    (strategy p).bob 2 = bobThird p := by
  simp [strategy, schmidtStrategy, SchmidtStrategy.toQuantumStrategy]

/-- Born contraction for a real Schmidt-diagonal state. -/
theorem schmidt_bornNumerator (S : SchmidtStrategy)
    (A B : Matrix (Fin S.dim) (Fin S.dim) ℂ) :
    S.toQuantumStrategy.bornNumerator A B =
      ∑ i : Fin S.dim, ∑ k : Fin S.dim,
        (S.amplitude i : ℂ) * (S.amplitude k : ℂ) * A i k * B i k := by
  classical
  unfold QuantumStrategy.bornNumerator SchmidtStrategy.toQuantumStrategy
  simp only [SchmidtStrategy.state]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_eq_single k]
    · simp [mul_assoc, mul_left_comm, mul_comm]
    · intro l hl hlk
      simp [Matrix.diagonal, Ne.symm hlk]
    · simp
  · intro j hj hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

theorem strategy_bornNumerator (p : PVChain)
    (A B : Matrix (Fin (pvDim p)) (Fin (pvDim p)) ℂ) :
    (strategy p).bornNumerator A B =
      ∑ i : Fin (pvDim p), ∑ k : Fin (pvDim p),
        (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
          A i k * B i k := by
  change (schmidtStrategy p).toQuantumStrategy.bornNumerator A B = _
  rw [schmidt_bornNumerator]
  rfl

theorem strategy_born_one_right (p : PVChain)
    (A : Matrix (Fin (pvDim p)) (Fin (pvDim p)) ℂ) :
    (strategy p).bornNumerator A 1 =
      ∑ i : Fin (pvDim p),
        (paddedAmplitude p i.val : ℂ) ^ 2 * A i i := by
  classical
  rw [strategy_bornNumerator]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · change (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p i.val : ℂ) *
      A i i * (if i = i then 1 else 0) = _
    rw [if_pos rfl]
    ring
  · intro k hk hki
    change (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
      A i k * (if i = k then 1 else 0) = 0
    rw [if_neg (Ne.symm hki)]
    ring
  · simp

theorem strategy_born_one_left (p : PVChain)
    (B : Matrix (Fin (pvDim p)) (Fin (pvDim p)) ℂ) :
    (strategy p).bornNumerator 1 B =
      ∑ i : Fin (pvDim p),
        (paddedAmplitude p i.val : ℂ) ^ 2 * B i i := by
  classical
  rw [strategy_bornNumerator]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · change (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p i.val : ℂ) *
      (if i = i then 1 else 0) * B i i = _
    rw [if_pos rfl]
    ring
  · intro k hk hki
    change (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
      (if i = k then 1 else 0) * B i k = 0
    rw [if_neg (Ne.symm hki)]
    ring
  · simp

theorem alice_first_sum_offdiag (p : PVChain)
    {i k : Fin (pvDim p)} (hik : i ≠ k) :
    (aliceEffect p (-1) neg_one_sq).matrix i k +
      (aliceEffect p 1 one_sq).matrix i k = 0 := by
  obtain ⟨u, rfl⟩ := (aliceFullEquiv p).surjective i
  obtain ⟨v, rfl⟩ := (aliceFullEquiv p).surjective k
  have huv : u ≠ v := fun h => hik (congrArg (aliceFullEquiv p) h)
  rcases u with u | u <;> rcases v with v | v
  · fin_cases u
    fin_cases v
    exact (huv rfl).elim
  · simp [aliceSource]
  · simp [aliceSource]
  · rcases u with ⟨a, x⟩
    rcases v with ⟨b, y⟩
    by_cases hab : a = b
    · subst b
      fin_cases x <;> fin_cases y
      · exact (huv rfl).elim
      · simp [aliceSource, aliceBlocks, pProjection, blockDiagonal, pBlock]
        ring
      · simp [aliceSource, aliceBlocks, pProjection, blockDiagonal, pBlock]
        ring
      · exact (huv rfl).elim
    · simp [aliceSource, blockDiagonal, hab]

theorem strategy_born_alice_sum (p : PVChain) :
    (strategy p).bornNumerator
        ((aliceEffect p (-1) neg_one_sq).matrix +
          (aliceEffect p 1 one_sq).matrix)
        ((bobEffect p (-1) neg_one_sq).matrix +
          (bobEffect p 1 one_sq).matrix) =
      ∑ i : Fin (pvDim p),
        (paddedAmplitude p i.val : ℂ) ^ 2 *
          ((aliceEffect p (-1) neg_one_sq).matrix i i +
            (aliceEffect p 1 one_sq).matrix i i) *
          ((bobEffect p (-1) neg_one_sq).matrix i i +
            (bobEffect p 1 one_sq).matrix i i) := by
  classical
  rw [strategy_bornNumerator]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.add_apply]
    ring
  · intro k hk hki
    simp only [Matrix.add_apply]
    rw [alice_first_sum_offdiag p (Ne.symm hki)]
    ring
  · simp

theorem diagonal_born_combination (p : PVChain) :
    -(strategy p).bornNumerator (aliceEffect p 1 one_sq).matrix 1
      -(strategy p).bornNumerator 1 (bobEffect p (-1) neg_one_sq).matrix
      -2 * (strategy p).bornNumerator 1 (bobEffect p 1 one_sq).matrix
      +(strategy p).bornNumerator
        ((aliceEffect p (-1) neg_one_sq).matrix +
          (aliceEffect p 1 one_sq).matrix)
        ((bobEffect p (-1) neg_one_sq).matrix +
          (bobEffect p 1 one_sq).matrix) =
      ∑ i : Fin (pvDim p),
        (paddedAmplitude p i.val : ℂ) ^ 2 * diagonalKernel p i := by
  rw [strategy_born_one_right, strategy_born_one_left,
    strategy_born_one_left, strategy_born_alice_sum]
  have hpoint : ∀ i : Fin (pvDim p),
      (paddedAmplitude p i.val : ℂ) ^ 2 * diagonalKernel p i =
        -((paddedAmplitude p i.val : ℂ) ^ 2 *
            (aliceEffect p 1 one_sq).matrix i i)
        -((paddedAmplitude p i.val : ℂ) ^ 2 *
            (bobEffect p (-1) neg_one_sq).matrix i i)
        -2 * ((paddedAmplitude p i.val : ℂ) ^ 2 *
            (bobEffect p 1 one_sq).matrix i i)
        +(paddedAmplitude p i.val : ℂ) ^ 2 *
          ((aliceEffect p (-1) neg_one_sq).matrix i i +
            (aliceEffect p 1 one_sq).matrix i i) *
          ((bobEffect p (-1) neg_one_sq).matrix i i +
            (bobEffect p 1 one_sq).matrix i i) := by
    intro i
    unfold diagonalKernel
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The odd-dimensional zero-padded version of the PV numerator. -/
noncomputable def paddedNumerator (p : PVChain) : ℝ :=
  (∑ i : Fin (pvDim p),
      d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
        (paddedAmplitude p i.val) ^ 2) +
    (∑ q : Fin p.n,
      s (paddedLabel p (2 * q.val + 2)) *
        paddedAmplitude p (2 * q.val + 1) *
        paddedAmplitude p (2 * q.val + 2)) +
    ∑ q : Fin p.n,
      s (paddedLabel p (2 * q.val + 1)) *
        paddedAmplitude p (2 * q.val) *
        paddedAmplitude p (2 * q.val + 1)

theorem diagonal_born_eq_cast (p : PVChain) :
    -(strategy p).bornNumerator (aliceEffect p 1 one_sq).matrix 1
      -(strategy p).bornNumerator 1 (bobEffect p (-1) neg_one_sq).matrix
      -2 * (strategy p).bornNumerator 1 (bobEffect p 1 one_sq).matrix
      +(strategy p).bornNumerator
        ((aliceEffect p (-1) neg_one_sq).matrix +
          (aliceEffect p 1 one_sq).matrix)
        ((bobEffect p (-1) neg_one_sq).matrix +
          (bobEffect p 1 one_sq).matrix) =
      ((∑ i : Fin (pvDim p),
        d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
          (paddedAmplitude p i.val) ^ 2 : ℝ) : ℂ) := by
  rw [diagonal_born_combination]
  simp_rw [diagonalKernel_eq]
  have hcast :
      ((∑ i : Fin (pvDim p),
        d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
          (paddedAmplitude p i.val) ^ 2 : ℝ) : ℂ) =
        ∑ i : Fin (pvDim p),
          ((d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
            (paddedAmplitude p i.val) ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.ofReal_sum Finset.univ
      (fun i : Fin (pvDim p) =>
        d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
          (paddedAmplitude p i.val) ^ 2)
  rw [hcast]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem even_born_eq_cast (p : PVChain) :
    (strategy p).bornNumerator
        ((aliceEffect p 1 one_sq).matrix -
          (aliceEffect p (-1) neg_one_sq).matrix)
        (bobThird p).matrix =
      ((∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 2)) *
          paddedAmplitude p (2 * q.val + 1) *
          paddedAmplitude p (2 * q.val + 2) : ℝ) : ℂ) := by
  rw [strategy_bornNumerator]
  simp only [Matrix.sub_apply]
  have hcast :
      ((∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 2)) *
          paddedAmplitude p (2 * q.val + 1) *
          paddedAmplitude p (2 * q.val + 2) : ℝ) : ℂ) =
        ∑ q : Fin p.n,
          (s (paddedLabel p (2 * q.val + 2)) : ℂ) *
            (paddedAmplitude p (2 * q.val + 1) : ℂ) *
            (paddedAmplitude p (2 * q.val + 2) : ℂ) := by
    calc
      _ = ∑ q : Fin p.n,
          ((s (paddedLabel p (2 * q.val + 2)) *
            paddedAmplitude p (2 * q.val + 1) *
            paddedAmplitude p (2 * q.val + 2) : ℝ) : ℂ) := by
          simpa using Complex.ofReal_sum Finset.univ
            (fun q : Fin p.n =>
              s (paddedLabel p (2 * q.val + 2)) *
                paddedAmplitude p (2 * q.val + 1) *
                paddedAmplitude p (2 * q.val + 2))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        push_cast
        rfl
  rw [hcast]
  calc
    _ = ∑ i, ∑ k,
        (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
          evenKernel p i k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      unfold evenKernel
      ring
    _ = _ := evenKernel_sum p

theorem odd_born_eq_cast (p : PVChain) :
    (strategy p).bornNumerator (aliceThird p).matrix
        ((bobEffect p 1 one_sq).matrix -
          (bobEffect p (-1) neg_one_sq).matrix) =
      ((∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 1)) *
          paddedAmplitude p (2 * q.val) *
          paddedAmplitude p (2 * q.val + 1) : ℝ) : ℂ) := by
  rw [strategy_bornNumerator]
  simp only [Matrix.sub_apply]
  have hcast :
      ((∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 1)) *
          paddedAmplitude p (2 * q.val) *
          paddedAmplitude p (2 * q.val + 1) : ℝ) : ℂ) =
        ∑ q : Fin p.n,
          (s (paddedLabel p (2 * q.val + 1)) : ℂ) *
            (paddedAmplitude p (2 * q.val) : ℂ) *
            (paddedAmplitude p (2 * q.val + 1) : ℂ) := by
    calc
      _ = ∑ q : Fin p.n,
          ((s (paddedLabel p (2 * q.val + 1)) *
            paddedAmplitude p (2 * q.val) *
            paddedAmplitude p (2 * q.val + 1) : ℝ) : ℂ) := by
          simpa using Complex.ofReal_sum Finset.univ
            (fun q : Fin p.n =>
              s (paddedLabel p (2 * q.val + 1)) *
                paddedAmplitude p (2 * q.val) *
                paddedAmplitude p (2 * q.val + 1))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        push_cast
        rfl
  rw [hcast]
  calc
    _ = ∑ i, ∑ k,
        (paddedAmplitude p i.val : ℂ) * (paddedAmplitude p k.val : ℂ) *
          oddKernel p i k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      unfold oddKernel
      ring
    _ = _ := oddKernel_sum p

theorem strategy_stateNormSq (p : PVChain) :
    (strategy p).stateNormSq = p.normSq := by
  unfold QuantumStrategy.stateNormSq strategy SchmidtStrategy.toQuantumStrategy
  rw [SchmidtStrategy.state_normSq]
  exact paddedAmplitude_normSq p

/-- The full neighbor sum before separating its even and odd edges. -/
noncomputable def neighborFull (p : PVChain) : ℝ :=
  ∑ r : Fin (p.n * 2),
    s (paddedLabel p (r.val + 1)) * paddedAmplitude p r.val *
      paddedAmplitude p (r.val + 1)

/-- Splitting the padded neighbor sum according to the two coordinates in
each consecutive pair gives precisely the two PV block contributions. -/
theorem neighborFull_eq_parts (p : PVChain) :
    neighborFull p =
      (∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 1)) *
          paddedAmplitude p (2 * q.val) *
          paddedAmplitude p (2 * q.val + 1)) +
      ∑ q : Fin p.n,
        s (paddedLabel p (2 * q.val + 2)) *
          paddedAmplitude p (2 * q.val + 1) *
          paddedAmplitude p (2 * q.val + 2) := by
  unfold neighborFull
  let e : Fin p.n × Fin 2 ≃ Fin (p.n * 2) := finProdFinEquiv
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp [e, finProdFinEquiv]
  ring

/-- Zero padding does not alter the original finite neighbor sum. -/
theorem neighborFull_eq_original (p : PVChain) :
    neighborFull p =
      ∑ i ∈ Finset.range (p.n - 1),
        s (p.label (i + 1)) * p.amplitude i * p.amplitude (i + 1) := by
  unfold neighborFull
  rw [Fin.sum_univ_eq_sum_range
    (fun r => s (paddedLabel p (r + 1)) * paddedAmplitude p r *
      paddedAmplitude p (r + 1)) (p.n * 2)]
  have hlen : p.n * 2 = (p.n - 1) + (p.n + 1) := by
    have hone : 1 ≤ p.n := p.n_pos
    have heq : p.n - 1 + 1 = p.n := Nat.sub_add_cancel hone
    omega
  rw [hlen, Finset.sum_range_add]
  have htail : (∑ x ∈ Finset.range (p.n + 1),
      s (paddedLabel p (p.n - 1 + x + 1)) *
        paddedAmplitude p (p.n - 1 + x) *
        paddedAmplitude p (p.n - 1 + x + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hone : 1 ≤ p.n := p.n_pos
    have heq : p.n - 1 + 1 = p.n := Nat.sub_add_cancel hone
    have hge : p.n ≤ p.n - 1 + x + 1 := by
      calc
        p.n = p.n - 1 + 1 := heq.symm
        _ ≤ p.n - 1 + x + 1 := by omega
    rw [paddedAmplitude_eq_zero p hge]
    ring
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < p.n - 1 := Finset.mem_range.mp hi
  have hi0 : i < p.n := by omega
  have hi1 : i + 1 < p.n := by omega
  rw [paddedAmplitude_eq p hi0, paddedAmplitude_eq p hi1]
  simp only [paddedLabel]
  rw [if_pos (by omega)]

/-- Zero padding does not alter the diagonal part of the PV numerator. -/
theorem paddedDiagonal_eq_original (p : PVChain) :
    (∑ i : Fin (pvDim p),
      d (paddedLabel p i.val) (paddedLabel p (i.val + 1)) *
        paddedAmplitude p i.val ^ 2) =
      ∑ i ∈ Finset.range p.n,
        d (p.label i) (p.label (i + 1)) * p.amplitude i ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => d (paddedLabel p i) (paddedLabel p (i + 1)) *
      paddedAmplitude p i ^ 2) (pvDim p)]
  have hdim : pvDim p = p.n + (p.n + 1) := by
    simp [pvDim]
    omega
  rw [hdim, Finset.sum_range_add]
  have htail : (∑ x ∈ Finset.range (p.n + 1),
      d (paddedLabel p (p.n + x)) (paddedLabel p (p.n + x + 1)) *
        paddedAmplitude p (p.n + x) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [paddedAmplitude_eq_zero]
    ring
    omega
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < p.n := Finset.mem_range.mp hi
  rw [paddedAmplitude_eq p hi']
  simp only [paddedLabel]
  rw [if_pos (by omega), if_pos (by omega)]

/-- The uniformly odd padding leaves the full PV numerator unchanged. -/
theorem paddedNumerator_eq (p : PVChain) :
    paddedNumerator p = p.numerator := by
  unfold paddedNumerator PVChain.numerator
  rw [paddedDiagonal_eq_original]
  rw [← neighborFull_eq_original]
  rw [neighborFull_eq_parts]
  ring

theorem pvBornNumerator_add_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A + C) B = S.bornNumerator A B + S.bornNumerator C B := by
  unfold QuantumStrategy.bornNumerator
  simp only [Matrix.add_apply]
  simp_rw [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]

theorem pvBornNumerator_add_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B + C) = S.bornNumerator A B + S.bornNumerator A C := by
  unfold QuantumStrategy.bornNumerator
  simp only [Matrix.add_apply]
  simp_rw [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]

theorem pvBornNumerator_sub_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A - C) B = S.bornNumerator A B - S.bornNumerator C B := by
  unfold QuantumStrategy.bornNumerator
  simp only [Matrix.sub_apply]
  simp_rw [mul_sub, sub_mul]
  simp only [Finset.sum_sub_distrib]

theorem pvBornNumerator_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B - C) = S.bornNumerator A B - S.bornNumerator A C := by
  unfold QuantumStrategy.bornNumerator
  simp only [Matrix.sub_apply]
  simp_rw [mul_sub, sub_mul]
  simp only [Finset.sum_sub_distrib]

theorem pvExpectation_add_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A + C) B = S.expectation A B + S.expectation C B := by
  unfold QuantumStrategy.expectation
  rw [pvBornNumerator_add_left]
  rw [Complex.add_re]
  ring

theorem pvExpectation_add_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (B + C) = S.expectation A B + S.expectation A C := by
  unfold QuantumStrategy.expectation
  rw [pvBornNumerator_add_right]
  rw [Complex.add_re]
  ring

theorem pvExpectation_sub_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A - C) B = S.expectation A B - S.expectation C B := by
  unfold QuantumStrategy.expectation
  rw [pvBornNumerator_sub_left]
  rw [Complex.sub_re]
  ring

theorem pvExpectation_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (B - C) = S.expectation A B - S.expectation A C := by
  unfold QuantumStrategy.expectation
  rw [pvBornNumerator_sub_right]
  rw [Complex.sub_re]
  ring

/-- The ten-term Bell expression grouped into its diagonal and two pairing parts. -/
theorem value_grouped (S : QuantumStrategy) :
    S.value =
      -S.expectation (S.alice 1).matrix 1
      -S.expectation 1 (S.bob 0).matrix
      -2 * S.expectation 1 (S.bob 1).matrix
      +S.expectation ((S.alice 0).matrix + (S.alice 1).matrix)
        ((S.bob 0).matrix + (S.bob 1).matrix)
      +S.expectation ((S.alice 1).matrix - (S.alice 0).matrix)
        (S.bob 2).matrix
      +S.expectation (S.alice 2).matrix
        ((S.bob 1).matrix - (S.bob 0).matrix) := by
  rw [pvExpectation_add_left, pvExpectation_add_right, pvExpectation_add_right,
    pvExpectation_sub_left, pvExpectation_sub_right]
  unfold QuantumStrategy.value QuantumStrategy.aliceMarginal
    QuantumStrategy.bobMarginal QuantumStrategy.joint
  ring

/-- The Bell value of the explicit strategy is the padded PV
expression divided by its (unchanged) squared norm. -/
theorem strategy_value_eq_padded (p : PVChain) :
    (strategy p).value = paddedNumerator p / p.normSq := by
  rw [value_grouped]
  have ha0 : (strategy p).alice 0 = aliceEffect p (-1) neg_one_sq := by
    simpa using strategy_alice_zero p
  have ha1 : (strategy p).alice 1 = aliceEffect p 1 one_sq := by
    simpa using strategy_alice_one p
  have ha2 : (strategy p).alice 2 = aliceThird p := strategy_alice_two p
  have hb0 : (strategy p).bob 0 = bobEffect p (-1) neg_one_sq := by
    simpa using strategy_bob_zero p
  have hb1 : (strategy p).bob 1 = bobEffect p 1 one_sq := by
    simpa using strategy_bob_one p
  have hb2 : (strategy p).bob 2 = bobThird p := strategy_bob_two p
  rw [ha0, ha1, ha2, hb0, hb1, hb2]
  unfold QuantumStrategy.expectation
  rw [strategy_stateNormSq]
  have hd := congrArg Complex.re (diagonal_born_eq_cast p)
  have he := congrArg Complex.re (even_born_eq_cast p)
  have ho := congrArg Complex.re (odd_born_eq_cast p)
  norm_num at hd he ho
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hd
  unfold paddedNumerator
  rw [← hd, ← he, ← ho]
  ring
  rfl

/-- The explicit complex finite-dimensional strategy realizes the exact PV
chain value. -/
theorem strategy_value (p : PVChain) :
    (strategy p).value = p.value := by
  rw [strategy_value_eq_padded, paddedNumerator_eq]
  rfl

/-- Terminal realization theorem in the canonical Schmidt presentation. -/
theorem schmidtStrategy_value (p : PVChain) :
    (schmidtStrategy p).value = p.value := by
  change (strategy p).value = p.value
  exact strategy_value p

/-- Every finite PV chain is realized by a finite-dimensional
Schmidt strategy. -/
theorem exists_schmidtStrategy (p : PVChain) :
    ∃ S : SchmidtStrategy, S.value = p.value :=
  ⟨schmidtStrategy p, schmidtStrategy_value p⟩

/-- The same realization, viewed in the fully general complex strategy type. -/
theorem exists_quantumStrategy (p : PVChain) :
    ∃ S : QuantumStrategy, S.value = p.value :=
  ⟨strategy p, strategy_value p⟩

end PVRealization
end I3322
