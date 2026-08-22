import I3322.PVRealization
import I3322.PVSupremum
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The finite-dimensional quantum supremum

This file defines the finite-dimensional quantum supremum and proves the
lower bound obtained from PV realization.
-/

namespace I3322

namespace QuantumSupremumAux

open scoped BigOperators ComplexOrder

/-- The complement of a binary projection, used only for the elementary
probability bound needed to make the raw quantum supremum well-defined. -/
def complementProjection {n : ℕ} (P : OrthogonalProjection n) :
    OrthogonalProjection n where
  matrix := 1 - P.matrix
  hermitian := by
    rw [Matrix.conjTranspose_sub, P.hermitian]
    ext i j
    simp [Matrix.one_apply]
  idempotent := by
    have hP := P.idempotent
    noncomm_ring
    rw [hP]
    module

@[simp] theorem complementProjection_matrix {n : ℕ}
    (P : OrthogonalProjection n) :
    (complementProjection P).matrix = 1 - P.matrix := rfl

/-- A Hermitian idempotent matrix is positive semidefinite. -/
theorem projection_posSemidef {n : ℕ} (P : OrthogonalProjection n) :
    P.matrix.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P.matrix
  rw [P.hermitian, P.idempotent] at h
  exact h

/-- Coefficient matrix regarded as a vector on the product basis. -/
def stateVector (S : QuantumStrategy) :
    (Fin S.dimA × Fin S.dimB) → ℂ :=
  fun ij => S.state ij.1 ij.2

/-- Product observable on the product basis. -/
def tensorOperator (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    Matrix (Fin S.dimA × Fin S.dimB) (Fin S.dimA × Fin S.dimB) ℂ :=
  A.kronecker B

theorem bornNumerator_eq_dotProduct (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A B =
      dotProduct (star (stateVector S))
        (Matrix.mulVec (tensorOperator S A B) (stateVector S)) := by
  classical
  simp only [QuantumStrategy.bornNumerator, stateVector, tensorOperator,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp [Matrix.kronecker]
  ring

theorem expectation_nonneg_of_posSemidef (S : QuantumStrategy)
    {A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ}
    {B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ S.expectation A B := by
  have hK : (tensorOperator S A B).PosSemidef := hA.kronecker hB
  have hq := hK.dotProduct_mulVec_nonneg (stateVector S)
  have hre : 0 ≤ (S.bornNumerator A B).re := by
    rw [bornNumerator_eq_dotProduct]
    exact (RCLike.nonneg_iff.mp hq).1
  exact div_nonneg hre S.stateNormSq_pos'.le

theorem bornNumerator_add_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A + C) B =
      S.bornNumerator A B + S.bornNumerator C B := by
  classical
  simp only [QuantumStrategy.bornNumerator, Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem bornNumerator_add_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B + C) =
      S.bornNumerator A B + S.bornNumerator A C := by
  classical
  simp only [QuantumStrategy.bornNumerator, Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem bornNumerator_sub_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A - C) B =
      S.bornNumerator A B - S.bornNumerator C B := by
  simp only [sub_eq_add_neg]
  rw [bornNumerator_add_left]
  simp [QuantumStrategy.bornNumerator]

theorem bornNumerator_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B - C) =
      S.bornNumerator A B - S.bornNumerator A C := by
  simp only [sub_eq_add_neg]
  rw [bornNumerator_add_right]
  simp [QuantumStrategy.bornNumerator]

theorem expectation_sub_left (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A - C) B =
      S.expectation A B - S.expectation C B := by
  rw [QuantumStrategy.expectation, QuantumStrategy.expectation,
    QuantumStrategy.expectation, bornNumerator_sub_left]
  simp only [Complex.sub_re]
  ring

theorem expectation_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B C : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (B - C) =
      S.expectation A B - S.expectation A C := by
  rw [QuantumStrategy.expectation, QuantumStrategy.expectation,
    QuantumStrategy.expectation, bornNumerator_sub_right]
  simp only [Complex.sub_re]
  ring

theorem bornNumerator_one_one (S : QuantumStrategy) :
    S.bornNumerator 1 1 = (S.stateNormSq : ℂ) := by
  classical
  simp [QuantumStrategy.bornNumerator, QuantumStrategy.stateNormSq,
    Matrix.one_apply, ← Complex.normSq_eq_conj_mul_self]

@[simp] theorem expectation_one_one (S : QuantumStrategy) :
    S.expectation 1 1 = 1 := by
  rw [QuantumStrategy.expectation, bornNumerator_one_one]
  simp [S.stateNormSq_ne_zero]

theorem projection_expectation_nonneg (S : QuantumStrategy)
    (P : OrthogonalProjection S.dimA)
    (Q : OrthogonalProjection S.dimB) :
    0 ≤ S.expectation P.matrix Q.matrix :=
  expectation_nonneg_of_posSemidef S
    (projection_posSemidef P) (projection_posSemidef Q)

theorem joint_nonneg (S : QuantumStrategy) (x y : Fin 3) :
    0 ≤ S.joint x y := by
  unfold QuantumStrategy.joint
  exact projection_expectation_nonneg S (S.alice x) (S.bob y)

theorem aliceMarginal_nonneg (S : QuantumStrategy) (x : Fin 3) :
    0 ≤ S.aliceMarginal x := by
  unfold QuantumStrategy.aliceMarginal
  change 0 ≤ S.expectation (S.alice x).matrix
    (OrthogonalProjection.one S.dimB).matrix
  exact projection_expectation_nonneg S (S.alice x)
    (OrthogonalProjection.one S.dimB)

theorem bobMarginal_nonneg (S : QuantumStrategy) (y : Fin 3) :
    0 ≤ S.bobMarginal y := by
  unfold QuantumStrategy.bobMarginal
  change 0 ≤ S.expectation (OrthogonalProjection.one S.dimA).matrix
    (S.bob y).matrix
  exact projection_expectation_nonneg S (OrthogonalProjection.one S.dimA)
    (S.bob y)

theorem aliceMarginal_le_one (S : QuantumStrategy) (x : Fin 3) :
    S.aliceMarginal x ≤ 1 := by
  have h := projection_expectation_nonneg S
    (complementProjection (S.alice x)) (OrthogonalProjection.one S.dimB)
  change 0 ≤ S.expectation (1 - (S.alice x).matrix) 1 at h
  rw [expectation_sub_left, expectation_one_one] at h
  simpa [QuantumStrategy.aliceMarginal] using h

theorem bobMarginal_le_one (S : QuantumStrategy) (y : Fin 3) :
    S.bobMarginal y ≤ 1 := by
  have h := projection_expectation_nonneg S (OrthogonalProjection.one S.dimA)
    (complementProjection (S.bob y))
  change 0 ≤ S.expectation 1 (1 - (S.bob y).matrix) at h
  rw [expectation_sub_right, expectation_one_one] at h
  simpa [QuantumStrategy.bobMarginal] using h

theorem joint_le_one (S : QuantumStrategy) (x y : Fin 3) :
    S.joint x y ≤ 1 := by
  have h := projection_expectation_nonneg S
    (complementProjection (S.alice x)) (S.bob y)
  change 0 ≤ S.expectation (1 - (S.alice x).matrix) (S.bob y).matrix at h
  rw [expectation_sub_left] at h
  have hm := bobMarginal_le_one S y
  unfold QuantumStrategy.joint QuantumStrategy.bobMarginal at *
  linarith

end QuantumSupremumAux

/-- The paper's `I_{3322}^*`, over all finite-dimensional projective
strategies represented by `QuantumStrategy`. -/
noncomputable def quantumSupremum : ℝ :=
  sSup (Set.range QuantumStrategy.value)

theorem quantumValues_nonempty :
    (Set.range QuantumStrategy.value).Nonempty := by
  exact ⟨QuantumStrategy.trivial.value, ⟨QuantumStrategy.trivial, rfl⟩⟩

/-- Every finite PV-chain value is the value of a quantum
strategy with explicit matrices. -/
theorem pvValue_mem_quantumValues (p : PVChain) :
    p.value ∈ Set.range QuantumStrategy.value := by
  obtain ⟨S, hS⟩ := PVRealization.exists_quantumStrategy p
  exact ⟨S, hS⟩

/-- A crude bound: all joint and marginal probabilities lie in
`[0,1]`, so retaining only the six positive joint terms bounds `I3322` by 6. -/
theorem quantumValue_le_six (S : QuantumStrategy) : S.value ≤ 6 := by
  have ha1 := QuantumSupremumAux.aliceMarginal_nonneg S 1
  have hb0 := QuantumSupremumAux.bobMarginal_nonneg S 0
  have hb1 := QuantumSupremumAux.bobMarginal_nonneg S 1
  have hj00n := QuantumSupremumAux.joint_nonneg S 0 0
  have hj01n := QuantumSupremumAux.joint_nonneg S 0 1
  have hj10n := QuantumSupremumAux.joint_nonneg S 1 0
  have hj11n := QuantumSupremumAux.joint_nonneg S 1 1
  have hj02n := QuantumSupremumAux.joint_nonneg S 0 2
  have hj12n := QuantumSupremumAux.joint_nonneg S 1 2
  have hj20n := QuantumSupremumAux.joint_nonneg S 2 0
  have hj21n := QuantumSupremumAux.joint_nonneg S 2 1
  have hj00u := QuantumSupremumAux.joint_le_one S 0 0
  have hj01u := QuantumSupremumAux.joint_le_one S 0 1
  have hj10u := QuantumSupremumAux.joint_le_one S 1 0
  have hj11u := QuantumSupremumAux.joint_le_one S 1 1
  have hj12u := QuantumSupremumAux.joint_le_one S 1 2
  have hj21u := QuantumSupremumAux.joint_le_one S 2 1
  unfold QuantumStrategy.value
  linarith

theorem quantumValues_bddAbove :
    BddAbove (Set.range QuantumStrategy.value) := by
  refine ⟨6, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact quantumValue_le_six S

/-- Explicit PV realization gives the reverse supremum
inequality. -/
theorem betaPV_le_quantumSupremum : betaPV ≤ quantumSupremum := by
  apply csSup_le pvValues_nonempty
  rintro _ ⟨p, rfl⟩
  exact le_csSup quantumValues_bddAbove (pvValue_mem_quantumValues p)

end I3322
