import I3322.QuantumStrategy
import I3322.SchmidtStrategy
import I3322.CouplingTable
import I3322.TableSymmetry
import I3322.FiniteCauchy
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NoncommRing
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.HermitianMat.Schatten

/-!
# Operator reduction for `I3322`

This file proves the operator-to-coupling-table reduction for
`I3322.QuantumStrategy`.

The first layer is completely basis-free: projections are converted to
reflections, the two elementary reflection relations are proved, Born
expectation is proved linear in both operators, and the probability form of
`I3322` is converted exactly to equation (13) of the manuscript.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Physlib's Schatten `1`-norm agrees with its trace norm. -/
theorem schattenNorm_one_eq_traceNorm (A : Matrix n n ℂ) :
    schattenNorm A 1 = A.traceNorm := by
  rw [schattenNorm_eq_sum_singularValues_rpow A (by positivity : (0 : ℝ) < 1),
    traceNorm_eq_sum_singularValues]
  norm_num

/-- The square of the Schatten `2`-norm is the Hilbert--Schmidt quadratic
form.  Stating this bridge explicitly keeps the only analytic inequality in
the table reduction tied to the concrete matrix entries. -/
theorem schattenNorm_two_rpow_eq_re_trace (A : Matrix n n ℂ) :
    schattenNorm A 2 ^ (2 : ℝ) = Complex.re ((A.conjTranspose * A).trace) := by
  let hH := Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
  rw [schattenNorm_rpow_eq_sum_singularValues A (by positivity : (0 : ℝ) < 2)]
  calc
    (∑ i : n, singularValues A i ^ (2 : ℝ)) =
        ∑ i : n, hH.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold singularValues
      rw [Real.rpow_two, Real.sq_sqrt]
      simpa [hH] using Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
    _ = Complex.re ((A.conjTranspose * A).trace) := by
      simpa using congrArg Complex.re hH.trace_eq_sum_eigenvalues.symm

/-- Schatten--Hölder at `(1,2,2)`, in the trace/Hilbert--Schmidt form
used in the manuscript. -/
theorem traceNorm_mul_le_schatten_two (A B : Matrix n n ℂ) :
    (A * B).traceNorm ≤ schattenNorm A 2 * schattenNorm B 2 := by
  rw [← schattenNorm_one_eq_traceNorm]
  exact schattenNorm_mul_le A B (by positivity) (by positivity) (by positivity) (by norm_num)

end Matrix

namespace I3322

open scoped BigOperators ComplexOrder

/-- Finite-sum algebra behind the coefficient
`d(a,b) = ab + (a-b)/2 - 1`.  Keeping it generic avoids any dependence
on the particular spectral-label representation. -/
theorem sum_sum_d_algebra {A B : Type*} [Fintype A] [Fintype B]
    (x : A → ℝ) (y : B → ℝ) (w : A → B → ℝ) :
    (∑ a, ∑ b, d (x a) (y b) * w a b) =
      -(∑ a, ∑ b, w a b) +
        ((∑ a, ∑ b, 2 * x a * w a b) -
          (∑ a, ∑ b, 2 * y b * w a b) +
          (∑ a, ∑ b, 4 * x a * y b * w a b)) / 4 := by
  classical
  calc
    _ = ∑ a, ∑ b,
        (-w a b + (2 * x a * w a b - 2 * y b * w a b +
          4 * x a * y b * w a b) / 4) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold d
      ring
    _ = _ := by
      have hsum_add (f g : A → B → ℝ) :
          (∑ a, ∑ b, (f a b + g a b)) =
            (∑ a, ∑ b, f a b) + (∑ a, ∑ b, g a b) := by
        simp only [Finset.sum_add_distrib]
      have hsum_neg (f : A → B → ℝ) :
          (∑ a, ∑ b, -f a b) = -(∑ a, ∑ b, f a b) := by
        simp only [Finset.sum_neg_distrib]
      have hsum_affine (f g h : A → B → ℝ) :
          (∑ a, ∑ b, (f a b - g a b + h a b) / 4) =
            ((∑ a, ∑ b, f a b) - (∑ a, ∑ b, g a b) +
              (∑ a, ∑ b, h a b)) / 4 := by
        simp only [div_eq_mul_inv]
        simp_rw [← Finset.sum_mul]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hsum_add, hsum_neg, hsum_affine]

namespace OrthogonalProjection

/-- The two-outcome reflection corresponding to an outcome-`1` projection. -/
def reflection {n : ℕ} (P : OrthogonalProjection n) :
    Matrix (Fin n) (Fin n) ℂ :=
  2 • P.matrix - 1

theorem reflection_hermitian {n : ℕ} (P : OrthogonalProjection n) :
    P.reflection.conjTranspose = P.reflection := by
  simp only [reflection, Matrix.conjTranspose_sub, Matrix.conjTranspose_nsmul,
    P.hermitian]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem reflection_sq {n : ℕ} (P : OrthogonalProjection n) :
    P.reflection * P.reflection = 1 := by
  rw [reflection]
  have hP := P.idempotent
  noncomm_ring
  rw [hP]
  simp

/-- Flip the two outcomes of a projective binary measurement. -/
def complement {n : ℕ} (P : OrthogonalProjection n) : OrthogonalProjection n where
  matrix := 1 - P.matrix
  hermitian := by
    rw [Matrix.conjTranspose_sub, P.hermitian]
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  idempotent := by
    have hP := P.idempotent
    noncomm_ring
    rw [hP]
    module

@[simp] theorem complement_matrix {n : ℕ} (P : OrthogonalProjection n) :
    P.complement.matrix = 1 - P.matrix := rfl

theorem complement_reflection {n : ℕ} (P : OrthogonalProjection n) :
    P.complement.reflection = -P.reflection := by
  unfold reflection complement
  noncomm_ring

end OrthogonalProjection

namespace QuantumStrategy

/-- The coefficient matrix regarded as the state vector on the product
index.  This is only a change of presentation; no normal-form hypothesis is
introduced. -/
def stateVector (S : QuantumStrategy) :
    (Fin S.dimA × Fin S.dimB) → ℂ :=
  fun ij => S.state ij.1 ij.2

/-- The matrix of a product observable on the product basis. -/
def tensorOperator (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    Matrix (Fin S.dimA × Fin S.dimB) (Fin S.dimA × Fin S.dimB) ℂ :=
  A.kronecker B

/-- The four-index Born contraction is the ordinary quadratic form of the
Kronecker-product observable.  This bridge allows the standard Hilbert-space
Cauchy--Schwarz inequality to be applied to the strategy model. -/
theorem bornNumerator_eq_dotProduct (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A B =
      dotProduct (star S.stateVector)
        (Matrix.mulVec (S.tensorOperator A B) S.stateVector) := by
  classical
  simp only [bornNumerator, stateVector, tensorOperator, dotProduct,
    Matrix.mulVec, Matrix.kronecker_apply, Pi.star_apply]
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

theorem bornNumerator_add_left (S : QuantumStrategy)
    (A A' : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A + A') B =
      S.bornNumerator A B + S.bornNumerator A' B := by
  classical
  simp only [bornNumerator, Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem bornNumerator_add_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B B' : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B + B') =
      S.bornNumerator A B + S.bornNumerator A B' := by
  classical
  simp only [bornNumerator, Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem bornNumerator_sub_left (S : QuantumStrategy)
    (A A' : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A - A') B =
      S.bornNumerator A B - S.bornNumerator A' B := by
  simp only [sub_eq_add_neg]
  rw [bornNumerator_add_left]
  simp [bornNumerator]

theorem bornNumerator_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B B' : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A (B - B') =
      S.bornNumerator A B - S.bornNumerator A B' := by
  simp only [sub_eq_add_neg]
  rw [bornNumerator_add_right]
  simp [bornNumerator]

theorem expectation_add_left (S : QuantumStrategy)
    (A A' : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A + A') B = S.expectation A B + S.expectation A' B := by
  rw [expectation, expectation, expectation, bornNumerator_add_left]
  simp only [Complex.add_re]
  ring

theorem expectation_add_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B B' : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (B + B') = S.expectation A B + S.expectation A B' := by
  rw [expectation, expectation, expectation, bornNumerator_add_right]
  simp only [Complex.add_re]
  ring

theorem expectation_sub_left (S : QuantumStrategy)
    (A A' : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A - A') B = S.expectation A B - S.expectation A' B := by
  rw [expectation, expectation, expectation, bornNumerator_sub_left]
  simp only [Complex.sub_re]
  ring

theorem expectation_sub_right (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B B' : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (B - B') = S.expectation A B - S.expectation A B' := by
  rw [expectation, expectation, expectation, bornNumerator_sub_right]
  simp only [Complex.sub_re]
  ring

theorem expectation_finset_sum_left (S : QuantumStrategy)
    {k : Type*} [DecidableEq k] (t : Finset k)
    (A : k → Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (∑ i ∈ t, A i) B = ∑ i ∈ t, S.expectation (A i) B := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [expectation, bornNumerator]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, S.expectation_add_left, ih]

theorem expectation_finset_sum_right (S : QuantumStrategy)
    {k : Type*} [DecidableEq k]
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (t : Finset k) (B : k → Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (∑ i ∈ t, B i) = ∑ i ∈ t, S.expectation A (B i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [expectation, bornNumerator]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, S.expectation_add_right, ih]

theorem expectation_sum_left (S : QuantumStrategy)
    {k : Type*} [Fintype k]
    (A : k → Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (∑ i, A i) B = ∑ i, S.expectation (A i) B := by
  classical
  simpa using S.expectation_finset_sum_left Finset.univ A B

theorem expectation_sum_right (S : QuantumStrategy)
    {k : Type*} [Fintype k]
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : k → Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A (∑ i, B i) = ∑ i, S.expectation A (B i) := by
  classical
  simpa using S.expectation_finset_sum_right A Finset.univ B

theorem bornNumerator_real_smul_left (S : QuantumStrategy) (x : ℝ)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator ((x : ℂ) • A) B = (x : ℂ) * S.bornNumerator A B := by
  classical
  simp only [bornNumerator, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem bornNumerator_real_smul_right (S : QuantumStrategy) (x : ℝ)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A ((x : ℂ) • B) = (x : ℂ) * S.bornNumerator A B := by
  classical
  simp only [bornNumerator, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem expectation_real_smul_left (S : QuantumStrategy) (x : ℝ)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation ((x : ℂ) • A) B = x * S.expectation A B := by
  rw [expectation, expectation, bornNumerator_real_smul_left]
  simp
  ring

theorem expectation_real_smul_right (S : QuantumStrategy) (x : ℝ)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation A ((x : ℂ) • B) = x * S.expectation A B := by
  rw [expectation, expectation, bornNumerator_real_smul_right]
  simp
  ring

theorem expectation_nonneg_of_posSemidef (S : QuantumStrategy)
    {A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ}
    {B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ S.expectation A B := by
  have hK : (S.tensorOperator A B).PosSemidef := by
    exact hA.kronecker hB
  have hq := hK.dotProduct_mulVec_nonneg S.stateVector
  have hre : 0 ≤ (S.bornNumerator A B).re := by
    rw [S.bornNumerator_eq_dotProduct]
    exact (RCLike.nonneg_iff.mp hq).1
  exact div_nonneg hre S.stateNormSq_pos'.le

theorem bornNumerator_one_one (S : QuantumStrategy) :
    S.bornNumerator 1 1 = (S.stateNormSq : ℂ) := by
  classical
  simp [bornNumerator, stateNormSq, Matrix.one_apply,
    ← Complex.normSq_eq_conj_mul_self]

@[simp] theorem expectation_one_one (S : QuantumStrategy) :
    S.expectation 1 1 = 1 := by
  rw [expectation, bornNumerator_one_one]
  simp [S.stateNormSq_ne_zero]

/-- Alice's three reflections. -/
def aliceReflection (S : QuantumStrategy) (x : Fin 3) :
    Matrix (Fin S.dimA) (Fin S.dimA) ℂ :=
  (S.alice x).reflection

/-- Bob's three reflections. -/
def bobReflection (S : QuantumStrategy) (y : Fin 3) :
    Matrix (Fin S.dimB) (Fin S.dimB) ℂ :=
  (S.bob y).reflection

/-- `p=a₁+a₂` in zero-based Lean indexing. -/
def p (S : QuantumStrategy) : Matrix (Fin S.dimA) (Fin S.dimA) ℂ :=
  S.aliceReflection 0 + S.aliceReflection 1

/-- `r=a₂-a₁` in zero-based Lean indexing. -/
def r (S : QuantumStrategy) : Matrix (Fin S.dimA) (Fin S.dimA) ℂ :=
  S.aliceReflection 1 - S.aliceReflection 0

/-- `q=b₁+b₂` in zero-based Lean indexing. -/
def q (S : QuantumStrategy) : Matrix (Fin S.dimB) (Fin S.dimB) ℂ :=
  S.bobReflection 0 + S.bobReflection 1

/-- `τ=b₂-b₁` in zero-based Lean indexing. -/
def tau (S : QuantumStrategy) : Matrix (Fin S.dimB) (Fin S.dimB) ℂ :=
  S.bobReflection 1 - S.bobReflection 0

theorem p_sq_add_r_sq (S : QuantumStrategy) :
    S.p * S.p + S.r * S.r = 4 • (1 : Matrix (Fin S.dimA) (Fin S.dimA) ℂ) := by
  unfold p r aliceReflection
  noncomm_ring
  rw [(S.alice 0).reflection_sq, (S.alice 1).reflection_sq]
  norm_num

theorem p_hermitian (S : QuantumStrategy) : S.p.IsHermitian := by
  unfold p aliceReflection OrthogonalProjection.reflection
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_nsmul]
  rw [(S.alice 0).hermitian, (S.alice 1).hermitian]
  congr 1 <;> ext i j <;>
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem r_hermitian (S : QuantumStrategy) : S.r.IsHermitian := by
  unfold r aliceReflection OrthogonalProjection.reflection
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_nsmul]
  rw [(S.alice 0).hermitian, (S.alice 1).hermitian]
  congr 1 <;> ext i j <;>
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

/-- Eigenvalues of `p`, in the orthonormal eigenbasis chosen by mathlib's
finite-dimensional Hermitian spectral theorem. -/
noncomputable def pEigenvalue (S : QuantumStrategy) : Fin S.dimA → ℝ :=
  S.p_hermitian.eigenvalues

/-- The unitary whose columns form the chosen eigenbasis of `p`. -/
noncomputable def pEigenvectorUnitary (S : QuantumStrategy) :
    Matrix.unitaryGroup (Fin S.dimA) ℂ :=
  S.p_hermitian.eigenvectorUnitary

theorem p_spectral_theorem (S : QuantumStrategy) :
    S.p = Unitary.conjStarAlgAut ℂ _ S.pEigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ S.pEigenvalue)) :=
  S.p_hermitian.spectral_theorem

theorem p_mulVec_eigenvector (S : QuantumStrategy) (j : Fin S.dimA) :
    Matrix.mulVec S.p ⇑(S.p_hermitian.eigenvectorBasis j) =
      (S.pEigenvalue j) • ⇑(S.p_hermitian.eigenvectorBasis j) :=
  S.p_hermitian.mulVec_eigenvectorBasis j

/-- The anticommutation relation sends the `p`-eigenspace at `μ` through
`r` into the eigenspace at `-μ`.  This is the algebraic core of the mirror
sector relation `r E_c = E_{-c} r`. -/
theorem p_mulVec_r_eigenvector (S : QuantumStrategy) (j : Fin S.dimA) :
    Matrix.mulVec S.p
        (Matrix.mulVec S.r ⇑(S.p_hermitian.eigenvectorBasis j)) =
      (-S.pEigenvalue j) •
        Matrix.mulVec S.r ⇑(S.p_hermitian.eigenvectorBasis j) := by
  let v : Fin S.dimA → ℂ := ⇑(S.p_hermitian.eigenvectorBasis j)
  have hanti :
      Matrix.mulVec S.p (Matrix.mulVec S.r v) +
          Matrix.mulVec S.r (Matrix.mulVec S.p v) = 0 := by
    calc
      _ = Matrix.mulVec (S.p * S.r + S.r * S.p) v := by
        simp [Matrix.add_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by
        have hpR : S.p * S.r + S.r * S.p = 0 := by
          unfold p r aliceReflection
          noncomm_ring
          rw [(S.alice 0).reflection_sq, (S.alice 1).reflection_sq]
          simp
        rw [hpR]
        simp
  calc
    Matrix.mulVec S.p (Matrix.mulVec S.r v) =
        -Matrix.mulVec S.r (Matrix.mulVec S.p v) :=
      eq_neg_of_add_eq_zero_left hanti
    _ = -Matrix.mulVec S.r ((S.pEigenvalue j) • v) := by
      rw [S.p_mulVec_eigenvector]
    _ = (-S.pEigenvalue j) • Matrix.mulVec S.r v := by
      rw [Matrix.mulVec_smul]
      simp

/-- On a `p` eigenvector, `r²` has the complementary squared magnitude
`4-μ²`. -/
theorem r_sq_mulVec_eigenvector (S : QuantumStrategy) (j : Fin S.dimA) :
    Matrix.mulVec S.r
        (Matrix.mulVec S.r ⇑(S.p_hermitian.eigenvectorBasis j)) =
      (4 - (S.pEigenvalue j) ^ 2) •
        ⇑(S.p_hermitian.eigenvectorBasis j) := by
  let v : Fin S.dimA → ℂ := ⇑(S.p_hermitian.eigenvectorBasis j)
  have hp : Matrix.mulVec S.p v = (S.pEigenvalue j) • v :=
    S.p_mulVec_eigenvector j
  have hp2 :
      Matrix.mulVec S.p (Matrix.mulVec S.p v) =
        ((S.pEigenvalue j) ^ 2) • v := by
    rw [hp, Matrix.mulVec_smul, hp]
    simp [smul_smul, pow_two]
  have hpair := congrArg (fun M : Matrix (Fin S.dimA) (Fin S.dimA) ℂ =>
      Matrix.mulVec M v) (S.p_sq_add_r_sq)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hpair
  rw [← Matrix.mulVec_mulVec v S.p S.p,
    ← Matrix.mulVec_mulVec v S.r S.r] at hpair
  rw [hp2] at hpair
  calc
    Matrix.mulVec S.r (Matrix.mulVec S.r v) =
        4 • v - (S.pEigenvalue j ^ 2) • v :=
      eq_sub_of_add_eq' hpair
    _ = (4 - S.pEigenvalue j ^ 2) • v := by module

/-- Consequently every block label `μ/2` lies in `[-1,1]`. -/
theorem pEigenvalue_sq_le_four (S : QuantumStrategy) (j : Fin S.dimA) :
    (S.pEigenvalue j) ^ 2 ≤ 4 := by
  let v : Fin S.dimA → ℂ := ⇑(S.p_hermitian.eigenvectorBasis j)
  have hrpsd : (S.r * S.r).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self S.r
    rw [S.r_hermitian] at h
    exact h
  have hnon := hrpsd.dotProduct_mulVec_nonneg v
  rw [← Matrix.mulVec_mulVec v S.r S.r,
    S.r_sq_mulVec_eigenvector j] at hnon
  have hv : dotProduct (star v) v = (1 : ℂ) := by
    dsimp [v]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simpa using
      (orthonormal_iff_ite.mp S.p_hermitian.eigenvectorBasis.orthonormal j j)
  rw [dotProduct_smul, hv] at hnon
  have hc : (((S.pEigenvalue j) ^ 2 : ℝ) : ℂ) ≤ (4 : ℂ) := by
    simpa [sub_nonneg] using hnon
  exact (RCLike.ofReal_le_ofReal (K := ℂ)).mp hc

/-- The block label is half the corresponding eigenvalue of `p`. -/
noncomputable def pEigenlabel (S : QuantumStrategy) (j : Fin S.dimA) : ℝ :=
  S.pEigenvalue j / 2

theorem pEigenlabel_mem (S : QuantumStrategy) (j : Fin S.dimA) :
    S.pEigenlabel j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hs := S.pEigenvalue_sq_le_four j
  constructor <;> unfold pEigenlabel <;> nlinarith [sq_nonneg (S.pEigenvalue j - 2),
    sq_nonneg (S.pEigenvalue j + 2)]

/-- The finite label set extracted from `p`, closed under reflection
`c ↦ -c` as required by the coupling-table construction. -/
noncomputable def pLabelFinset (S : QuantumStrategy) : Finset ℝ :=
  Finset.univ.image S.pEigenlabel ∪
    Finset.univ.image (fun j => -S.pEigenlabel j)

/-- Distinct scalar labels, rather than eigenvector indices; repeated
eigenvalues are therefore aggregated into one sector. -/
def PLabel (S : QuantumStrategy) := {c : ℝ // c ∈ S.pLabelFinset}

noncomputable instance (S : QuantumStrategy) : Fintype S.PLabel :=
  Fintype.ofFinset S.pLabelFinset (fun _ => Iff.rfl)

noncomputable def PLabel.value (S : QuantumStrategy) : S.PLabel → ℝ :=
  Subtype.val

theorem PLabel.value_injective (S : QuantumStrategy) :
    Function.Injective (PLabel.value S) := Subtype.val_injective

theorem PLabel.value_mem (S : QuantumStrategy) (c : S.PLabel) :
    PLabel.value S c ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Finset.mem_union.mp c.property with h | h
  · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
    simpa [PLabel.value, hj] using S.pEigenlabel_mem j
  · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
    have hm := S.pEigenlabel_mem j
    constructor <;> simp only [PLabel.value, hj] <;> linarith [hm.1, hm.2]

theorem p_mul_r_add_r_mul_p (S : QuantumStrategy) :
    S.p * S.r + S.r * S.p = 0 := by
  unfold p r aliceReflection
  noncomm_ring
  rw [(S.alice 0).reflection_sq, (S.alice 1).reflection_sq]
  simp

theorem q_sq_add_tau_sq (S : QuantumStrategy) :
    S.q * S.q + S.tau * S.tau = 4 • (1 : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) := by
  unfold q tau bobReflection
  noncomm_ring
  rw [(S.bob 0).reflection_sq, (S.bob 1).reflection_sq]
  norm_num

theorem q_mul_tau_add_tau_mul_q (S : QuantumStrategy) :
    S.q * S.tau + S.tau * S.q = 0 := by
  unfold q tau bobReflection
  noncomm_ring
  rw [(S.bob 0).reflection_sq, (S.bob 1).reflection_sq]
  simp

theorem q_hermitian (S : QuantumStrategy) : S.q.IsHermitian := by
  unfold q bobReflection OrthogonalProjection.reflection
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_nsmul]
  rw [(S.bob 0).hermitian, (S.bob 1).hermitian]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply]

theorem tau_hermitian (S : QuantumStrategy) : S.tau.IsHermitian := by
  unfold tau bobReflection OrthogonalProjection.reflection
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_nsmul]
  rw [(S.bob 0).hermitian, (S.bob 1).hermitian]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply]

noncomputable def qEigenvalue (S : QuantumStrategy) : Fin S.dimB → ℝ :=
  S.q_hermitian.eigenvalues

noncomputable def qEigenvectorUnitary (S : QuantumStrategy) :
    Matrix.unitaryGroup (Fin S.dimB) ℂ :=
  S.q_hermitian.eigenvectorUnitary

theorem q_mulVec_eigenvector (S : QuantumStrategy) (j : Fin S.dimB) :
    Matrix.mulVec S.q ⇑(S.q_hermitian.eigenvectorBasis j) =
      (S.qEigenvalue j) • ⇑(S.q_hermitian.eigenvectorBasis j) :=
  S.q_hermitian.mulVec_eigenvectorBasis j

theorem q_mulVec_tau_eigenvector (S : QuantumStrategy) (j : Fin S.dimB) :
    Matrix.mulVec S.q
        (Matrix.mulVec S.tau ⇑(S.q_hermitian.eigenvectorBasis j)) =
      (-S.qEigenvalue j) •
        Matrix.mulVec S.tau ⇑(S.q_hermitian.eigenvectorBasis j) := by
  let v : Fin S.dimB → ℂ := ⇑(S.q_hermitian.eigenvectorBasis j)
  have hanti :
      Matrix.mulVec S.q (Matrix.mulVec S.tau v) +
          Matrix.mulVec S.tau (Matrix.mulVec S.q v) = 0 := by
    calc
      _ = Matrix.mulVec (S.q * S.tau + S.tau * S.q) v := by
        simp [Matrix.add_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [S.q_mul_tau_add_tau_mul_q]; simp
  calc
    Matrix.mulVec S.q (Matrix.mulVec S.tau v) =
        -Matrix.mulVec S.tau (Matrix.mulVec S.q v) :=
      eq_neg_of_add_eq_zero_left hanti
    _ = -Matrix.mulVec S.tau ((S.qEigenvalue j) • v) := by
      rw [S.q_mulVec_eigenvector]
    _ = (-S.qEigenvalue j) • Matrix.mulVec S.tau v := by
      rw [Matrix.mulVec_smul]
      simp

theorem tau_sq_mulVec_eigenvector (S : QuantumStrategy) (j : Fin S.dimB) :
    Matrix.mulVec S.tau
        (Matrix.mulVec S.tau ⇑(S.q_hermitian.eigenvectorBasis j)) =
      (4 - (S.qEigenvalue j) ^ 2) •
        ⇑(S.q_hermitian.eigenvectorBasis j) := by
  let v : Fin S.dimB → ℂ := ⇑(S.q_hermitian.eigenvectorBasis j)
  have hq : Matrix.mulVec S.q v = (S.qEigenvalue j) • v :=
    S.q_mulVec_eigenvector j
  have hq2 :
      Matrix.mulVec S.q (Matrix.mulVec S.q v) =
        ((S.qEigenvalue j) ^ 2) • v := by
    rw [hq, Matrix.mulVec_smul, hq]
    simp [smul_smul, pow_two]
  have hpair := congrArg (fun M : Matrix (Fin S.dimB) (Fin S.dimB) ℂ ↦
      Matrix.mulVec M v) (S.q_sq_add_tau_sq)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hpair
  rw [← Matrix.mulVec_mulVec v S.q S.q,
    ← Matrix.mulVec_mulVec v S.tau S.tau] at hpair
  rw [hq2] at hpair
  calc
    Matrix.mulVec S.tau (Matrix.mulVec S.tau v) =
        4 • v - (S.qEigenvalue j ^ 2) • v :=
      eq_sub_of_add_eq' hpair
    _ = (4 - S.qEigenvalue j ^ 2) • v := by module

theorem qEigenvalue_sq_le_four (S : QuantumStrategy) (j : Fin S.dimB) :
    (S.qEigenvalue j) ^ 2 ≤ 4 := by
  let v : Fin S.dimB → ℂ := ⇑(S.q_hermitian.eigenvectorBasis j)
  have htpsd : (S.tau * S.tau).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self S.tau
    rw [S.tau_hermitian] at h
    exact h
  have hnon := htpsd.dotProduct_mulVec_nonneg v
  rw [← Matrix.mulVec_mulVec v S.tau S.tau,
    S.tau_sq_mulVec_eigenvector j] at hnon
  have hv : dotProduct (star v) v = (1 : ℂ) := by
    dsimp [v]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simpa using
      (orthonormal_iff_ite.mp S.q_hermitian.eigenvectorBasis.orthonormal j j)
  rw [dotProduct_smul, hv] at hnon
  have hc : (((S.qEigenvalue j) ^ 2 : ℝ) : ℂ) ≤ (4 : ℂ) := by
    simpa [sub_nonneg] using hnon
  exact (RCLike.ofReal_le_ofReal (K := ℂ)).mp hc

noncomputable def qEigenlabel (S : QuantumStrategy) (j : Fin S.dimB) : ℝ :=
  S.qEigenvalue j / 2

theorem qEigenlabel_mem (S : QuantumStrategy) (j : Fin S.dimB) :
    S.qEigenlabel j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hs := S.qEigenvalue_sq_le_four j
  constructor <;> unfold qEigenlabel <;> nlinarith [sq_nonneg (S.qEigenvalue j - 2),
    sq_nonneg (S.qEigenvalue j + 2)]

/-- A common finite scalar label set for the spectral decompositions of
`p` and `q`, closed under `c ↦ -c`.  Labels absent from one side simply
have a zero spectral projector on that side. -/
noncomputable def spectralLabelFinset (S : QuantumStrategy) : Finset ℝ :=
  (Finset.univ.image S.pEigenlabel ∪
      Finset.univ.image (fun i ↦ -S.pEigenlabel i)) ∪
    (Finset.univ.image S.qEigenlabel ∪
      Finset.univ.image (fun j ↦ -S.qEigenlabel j))

def SpectralLabel (S : QuantumStrategy) :=
  {c : ℝ // c ∈ S.spectralLabelFinset}

noncomputable instance (S : QuantumStrategy) : Fintype S.SpectralLabel :=
  Fintype.ofFinset S.spectralLabelFinset (fun _ ↦ Iff.rfl)

noncomputable def SpectralLabel.value (S : QuantumStrategy) :
    S.SpectralLabel → ℝ := Subtype.val

theorem SpectralLabel.value_injective (S : QuantumStrategy) :
    Function.Injective (SpectralLabel.value S) := Subtype.val_injective

theorem spectralLabel_neg_mem (S : QuantumStrategy) (c : S.SpectralLabel) :
    -c.1 ∈ S.spectralLabelFinset := by
  rcases Finset.mem_union.mp c.2 with hp | hq
  · rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
      rw [← hi]
      simp [spectralLabelFinset]
    · rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
      rw [← hi]
      simp [spectralLabelFinset]
  · rcases Finset.mem_union.mp hq with h | h
    · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
      rw [← hj]
      simp [spectralLabelFinset]
    · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
      rw [← hj]
      simp [spectralLabelFinset]

/-- Negation as an involutive permutation of the common label set. -/
noncomputable def SpectralLabel.neg (S : QuantumStrategy) :
    S.SpectralLabel → S.SpectralLabel :=
  fun c ↦ ⟨-c.1, S.spectralLabel_neg_mem c⟩

@[simp] theorem SpectralLabel.neg_value (S : QuantumStrategy) (c : S.SpectralLabel) :
    (SpectralLabel.neg S c).1 = -c.1 := rfl

@[simp] theorem SpectralLabel.neg_neg (S : QuantumStrategy) (c : S.SpectralLabel) :
    SpectralLabel.neg S (SpectralLabel.neg S c) = c := by
  apply Subtype.ext
  simp

noncomputable def SpectralLabel.negEquiv (S : QuantumStrategy) :
    S.SpectralLabel ≃ S.SpectralLabel where
  toFun := SpectralLabel.neg S
  invFun := SpectralLabel.neg S
  left_inv := SpectralLabel.neg_neg S
  right_inv := SpectralLabel.neg_neg S

theorem SpectralLabel.value_mem (S : QuantumStrategy) (c : S.SpectralLabel) :
    SpectralLabel.value S c ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Finset.mem_union.mp c.2 with hp | hq
  · rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
      simpa [SpectralLabel.value, hi] using S.pEigenlabel_mem i
    · rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
      have hm := S.pEigenlabel_mem i
      constructor <;> simp only [SpectralLabel.value, hi] <;> linarith [hm.1, hm.2]
  · rcases Finset.mem_union.mp hq with h | h
    · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
      simpa [SpectralLabel.value, hj] using S.qEigenlabel_mem j
    · rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
      have hm := S.qEigenlabel_mem j
      constructor <;> simp only [SpectralLabel.value, hj] <;> linarith [hm.1, hm.2]

/-- Diagonal mask selecting Alice eigenvectors with scalar label `c`. -/
noncomputable def aliceEigenMask (S : QuantumStrategy) (c : S.SpectralLabel) :
    Matrix (Fin S.dimA) (Fin S.dimA) ℂ :=
  Matrix.diagonal fun i ↦ if S.pEigenlabel i = c.1 then 1 else 0

/-- Alice's spectral projector for the `p`-eigenvalue `2c`. -/
noncomputable def aliceSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    Matrix (Fin S.dimA) (Fin S.dimA) ℂ :=
  S.pEigenvectorUnitary.val * S.aliceEigenMask c *
    S.pEigenvectorUnitary.val.conjTranspose

/-- Diagonal mask selecting Bob eigenvectors with scalar label `c`. -/
noncomputable def bobEigenMask (S : QuantumStrategy) (c : S.SpectralLabel) :
    Matrix (Fin S.dimB) (Fin S.dimB) ℂ :=
  Matrix.diagonal fun j ↦ if S.qEigenlabel j = c.1 then 1 else 0

/-- Bob's spectral projector for the `q`-eigenvalue `2c`. -/
noncomputable def bobSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    Matrix (Fin S.dimB) (Fin S.dimB) ℂ :=
  S.qEigenvectorUnitary.val * S.bobEigenMask c *
    S.qEigenvectorUnitary.val.conjTranspose

@[simp] theorem aliceEigenMask_conjTranspose (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    (S.aliceEigenMask c).conjTranspose = S.aliceEigenMask c := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : S.pEigenlabel i = c.1 <;>
      simp [aliceEigenMask, Matrix.conjTranspose_apply, Matrix.diagonal, hi]
  · simp [aliceEigenMask, Matrix.conjTranspose_apply, Matrix.diagonal, hij, Ne.symm hij]

@[simp] theorem aliceEigenMask_mul_self (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.aliceEigenMask c * S.aliceEigenMask c = S.aliceEigenMask c := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : S.pEigenlabel i = c.1 <;>
      simp [aliceEigenMask, Matrix.mul_apply, Matrix.diagonal, hi]
  · simp [aliceEigenMask, Matrix.mul_apply, Matrix.diagonal, hij]

@[simp] theorem bobEigenMask_conjTranspose (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    (S.bobEigenMask c).conjTranspose = S.bobEigenMask c := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : S.qEigenlabel i = c.1 <;>
      simp [bobEigenMask, Matrix.conjTranspose_apply, Matrix.diagonal, hi]
  · simp [bobEigenMask, Matrix.conjTranspose_apply, Matrix.diagonal, hij, Ne.symm hij]

@[simp] theorem bobEigenMask_mul_self (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.bobEigenMask c * S.bobEigenMask c = S.bobEigenMask c := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : S.qEigenlabel i = c.1 <;>
      simp [bobEigenMask, Matrix.mul_apply, Matrix.diagonal, hi]
  · simp [bobEigenMask, Matrix.mul_apply, Matrix.diagonal, hij]

theorem aliceSector_hermitian (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.aliceSector c).IsHermitian := by
  unfold aliceSector Matrix.IsHermitian
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem bobSector_hermitian (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.bobSector c).IsHermitian := by
  unfold bobSector Matrix.IsHermitian
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem aliceSector_idempotent (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.aliceSector c * S.aliceSector c = S.aliceSector c := by
  have hU : S.pEigenvectorUnitary.val.conjTranspose *
      S.pEigenvectorUnitary.val = 1 := by
    exact (Matrix.mem_unitaryGroup_iff_isometry S.pEigenvectorUnitary.val).mp
      S.pEigenvectorUnitary.prop |>.1
  unfold aliceSector
  rw [show
      (S.pEigenvectorUnitary.val * S.aliceEigenMask c *
          S.pEigenvectorUnitary.val.conjTranspose) *
          (S.pEigenvectorUnitary.val * S.aliceEigenMask c *
            S.pEigenvectorUnitary.val.conjTranspose) =
        S.pEigenvectorUnitary.val * S.aliceEigenMask c *
          (S.pEigenvectorUnitary.val.conjTranspose *
            S.pEigenvectorUnitary.val) * S.aliceEigenMask c *
              S.pEigenvectorUnitary.val.conjTranspose by noncomm_ring]
  rw [hU]
  simp [Matrix.mul_assoc]

theorem bobSector_idempotent (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.bobSector c * S.bobSector c = S.bobSector c := by
  have hU : S.qEigenvectorUnitary.val.conjTranspose *
      S.qEigenvectorUnitary.val = 1 := by
    exact (Matrix.mem_unitaryGroup_iff_isometry S.qEigenvectorUnitary.val).mp
      S.qEigenvectorUnitary.prop |>.1
  unfold bobSector
  rw [show
      (S.qEigenvectorUnitary.val * S.bobEigenMask c *
          S.qEigenvectorUnitary.val.conjTranspose) *
          (S.qEigenvectorUnitary.val * S.bobEigenMask c *
            S.qEigenvectorUnitary.val.conjTranspose) =
        S.qEigenvectorUnitary.val * S.bobEigenMask c *
          (S.qEigenvectorUnitary.val.conjTranspose *
            S.qEigenvectorUnitary.val) * S.bobEigenMask c *
              S.qEigenvectorUnitary.val.conjTranspose by noncomm_ring]
  rw [hU]
  simp [Matrix.mul_assoc]

theorem aliceSector_posSemidef (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.aliceSector c).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (S.aliceSector c)
  rw [S.aliceSector_hermitian c, S.aliceSector_idempotent c] at h
  exact h

theorem bobSector_posSemidef (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.bobSector c).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (S.bobSector c)
  rw [S.bobSector_hermitian c, S.bobSector_idempotent c] at h
  exact h

noncomputable def pEigenlabelAsSpectral (S : QuantumStrategy) (i : Fin S.dimA) :
    S.SpectralLabel :=
  ⟨S.pEigenlabel i, by simp [spectralLabelFinset]⟩

noncomputable def qEigenlabelAsSpectral (S : QuantumStrategy) (j : Fin S.dimB) :
    S.SpectralLabel :=
  ⟨S.qEigenlabel j, by simp [spectralLabelFinset]⟩

theorem sum_aliceEigenMask (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, S.aliceEigenMask c = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single (S.pEigenlabelAsSpectral i)]
    · simp [aliceEigenMask, pEigenlabelAsSpectral]
    · intro c _ hc
      have hne : S.pEigenlabel i ≠ c.1 := by
        intro h
        apply hc
        apply Subtype.ext
        exact h.symm
      simp [aliceEigenMask, hne]
    · simp
  · simp [Matrix.sum_apply, aliceEigenMask, Matrix.diagonal, hij]

theorem sum_bobEigenMask (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, S.bobEigenMask c = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single (S.qEigenlabelAsSpectral i)]
    · simp [bobEigenMask, qEigenlabelAsSpectral]
    · intro c _ hc
      have hne : S.qEigenlabel i ≠ c.1 := by
        intro h
        apply hc
        apply Subtype.ext
        exact h.symm
      simp [bobEigenMask, hne]
    · simp
  · simp [Matrix.sum_apply, bobEigenMask, Matrix.diagonal, hij]

theorem sum_aliceSector (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, S.aliceSector c = 1 := by
  classical
  unfold aliceSector
  rw [← Finset.sum_mul, ← Finset.mul_sum, S.sum_aliceEigenMask]
  have hU : S.pEigenvectorUnitary.val *
      S.pEigenvectorUnitary.val.conjTranspose = 1 := by
    have h := Unitary.coe_mul_star_self S.pEigenvectorUnitary
    change S.pEigenvectorUnitary.val *
      S.pEigenvectorUnitary.val.conjTranspose = 1 at h
    exact h
  simpa using hU

theorem sum_bobSector (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, S.bobSector c = 1 := by
  classical
  unfold bobSector
  rw [← Finset.sum_mul, ← Finset.mul_sum, S.sum_bobEigenMask]
  have hU : S.qEigenvectorUnitary.val *
      S.qEigenvectorUnitary.val.conjTranspose = 1 := by
    have h := Unitary.coe_mul_star_self S.qEigenvectorUnitary
    change S.qEigenvectorUnitary.val *
      S.qEigenvectorUnitary.val.conjTranspose = 1 at h
    exact h
  simpa using hU

theorem weighted_sum_aliceEigenMask (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, ((2 * c.1 : ℝ) : ℂ) • S.aliceEigenMask c =
      Matrix.diagonal (RCLike.ofReal ∘ S.pEigenvalue) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single (S.pEigenlabelAsSpectral i)]
    · simp [aliceEigenMask, pEigenlabelAsSpectral, pEigenlabel]
      ring
    · intro c _ hc
      have hne : S.pEigenlabel i ≠ c.1 := by
        intro h
        apply hc
        apply Subtype.ext
        exact h.symm
      simp [aliceEigenMask, hne]
    · simp
  · simp [Matrix.sum_apply, aliceEigenMask, Matrix.diagonal, hij]

theorem weighted_sum_bobEigenMask (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, ((2 * c.1 : ℝ) : ℂ) • S.bobEigenMask c =
      Matrix.diagonal (RCLike.ofReal ∘ S.qEigenvalue) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single (S.qEigenlabelAsSpectral i)]
    · simp [bobEigenMask, qEigenlabelAsSpectral, qEigenlabel]
      ring
    · intro c _ hc
      have hne : S.qEigenlabel i ≠ c.1 := by
        intro h
        apply hc
        apply Subtype.ext
        exact h.symm
      simp [bobEigenMask, hne]
    · simp
  · simp [Matrix.sum_apply, bobEigenMask, Matrix.diagonal, hij]

theorem p_eq_sum_sectors (S : QuantumStrategy) :
    S.p = ∑ c : S.SpectralLabel,
      ((2 * c.1 : ℝ) : ℂ) • S.aliceSector c := by
  classical
  rw [S.p_spectral_theorem, Unitary.conjStarAlgAut_apply]
  change S.pEigenvectorUnitary.val *
      Matrix.diagonal (RCLike.ofReal ∘ S.pEigenvalue) *
        S.pEigenvectorUnitary.val.conjTranspose = _
  rw [← S.weighted_sum_aliceEigenMask]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  unfold aliceSector
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem q_eq_sum_sectors (S : QuantumStrategy) :
    S.q = ∑ c : S.SpectralLabel,
      ((2 * c.1 : ℝ) : ℂ) • S.bobSector c := by
  classical
  rw [S.q_hermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change S.qEigenvectorUnitary.val *
      Matrix.diagonal (RCLike.ofReal ∘ S.qEigenvalue) *
        S.qEigenvectorUnitary.val.conjTranspose = _
  rw [← S.weighted_sum_bobEigenMask]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  unfold bobSector
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem aliceEigenMask_mul_eq_zero (S : QuantumStrategy)
    {c d : S.SpectralLabel} (hcd : c ≠ d) :
    S.aliceEigenMask c * S.aliceEigenMask d = 0 := by
  classical
  rw [aliceEigenMask, aliceEigenMask, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hc : S.pEigenlabel i = c.1
    · have hd : S.pEigenlabel i ≠ d.1 := by
        intro hid
        apply hcd
        apply Subtype.ext
        exact hc.symm.trans hid
      simp [Matrix.diagonal_apply, hc, hd]
      exact hcd
    · simp [Matrix.diagonal_apply, hc]
  · simp [Matrix.diagonal_apply, hij]

theorem bobEigenMask_mul_eq_zero (S : QuantumStrategy)
    {c d : S.SpectralLabel} (hcd : c ≠ d) :
    S.bobEigenMask c * S.bobEigenMask d = 0 := by
  classical
  rw [bobEigenMask, bobEigenMask, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hc : S.qEigenlabel i = c.1
    · have hd : S.qEigenlabel i ≠ d.1 := by
        intro hid
        apply hcd
        apply Subtype.ext
        exact hc.symm.trans hid
      simp [Matrix.diagonal_apply, hc, hd]
      exact hcd
    · simp [Matrix.diagonal_apply, hc]
  · simp [Matrix.diagonal_apply, hij]

theorem aliceSector_mul_eq_zero (S : QuantumStrategy)
    {c d : S.SpectralLabel} (hcd : c ≠ d) :
    S.aliceSector c * S.aliceSector d = 0 := by
  have hU : S.pEigenvectorUnitary.val.conjTranspose *
      S.pEigenvectorUnitary.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry S.pEigenvectorUnitary.val).mp
      S.pEigenvectorUnitary.prop |>.1
  unfold aliceSector
  calc
    _ = S.pEigenvectorUnitary.val * S.aliceEigenMask c *
          (S.pEigenvectorUnitary.val.conjTranspose *
            S.pEigenvectorUnitary.val) * S.aliceEigenMask d *
              S.pEigenvectorUnitary.val.conjTranspose := by noncomm_ring
    _ = S.pEigenvectorUnitary.val *
        (S.aliceEigenMask c * S.aliceEigenMask d) *
          S.pEigenvectorUnitary.val.conjTranspose := by
      rw [hU]
      simp [Matrix.mul_assoc]
    _ = 0 := by rw [S.aliceEigenMask_mul_eq_zero hcd]; simp

theorem bobSector_mul_eq_zero (S : QuantumStrategy)
    {c d : S.SpectralLabel} (hcd : c ≠ d) :
    S.bobSector c * S.bobSector d = 0 := by
  have hU : S.qEigenvectorUnitary.val.conjTranspose *
      S.qEigenvectorUnitary.val = 1 :=
    (Matrix.mem_unitaryGroup_iff_isometry S.qEigenvectorUnitary.val).mp
      S.qEigenvectorUnitary.prop |>.1
  unfold bobSector
  calc
    _ = S.qEigenvectorUnitary.val * S.bobEigenMask c *
          (S.qEigenvectorUnitary.val.conjTranspose *
            S.qEigenvectorUnitary.val) * S.bobEigenMask d *
              S.qEigenvectorUnitary.val.conjTranspose := by noncomm_ring
    _ = S.qEigenvectorUnitary.val *
        (S.bobEigenMask c * S.bobEigenMask d) *
          S.qEigenvectorUnitary.val.conjTranspose := by
      rw [hU]
      simp [Matrix.mul_assoc]
    _ = 0 := by rw [S.bobEigenMask_mul_eq_zero hcd]; simp

theorem p_mul_aliceSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.p * S.aliceSector c =
      (((2 * c.1 : ℝ) : ℂ) • S.aliceSector c) := by
  classical
  rw [S.p_eq_sum_sectors, Finset.sum_mul]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.smul_mul, S.aliceSector_idempotent]
  · intro d _ hdc
    rw [Matrix.smul_mul, S.aliceSector_mul_eq_zero hdc]
    simp
  · simp

theorem aliceSector_mul_p (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.aliceSector c * S.p =
      (((2 * c.1 : ℝ) : ℂ) • S.aliceSector c) := by
  classical
  rw [S.p_eq_sum_sectors, Finset.mul_sum]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.mul_smul, S.aliceSector_idempotent]
  · intro d _ hdc
    rw [Matrix.mul_smul, S.aliceSector_mul_eq_zero (Ne.symm hdc)]
    simp
  · simp

theorem q_mul_bobSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.q * S.bobSector c =
      (((2 * c.1 : ℝ) : ℂ) • S.bobSector c) := by
  classical
  rw [S.q_eq_sum_sectors, Finset.sum_mul]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.smul_mul, S.bobSector_idempotent]
  · intro d _ hdc
    rw [Matrix.smul_mul, S.bobSector_mul_eq_zero hdc]
    simp
  · simp

theorem bobSector_mul_q (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.bobSector c * S.q =
      (((2 * c.1 : ℝ) : ℂ) • S.bobSector c) := by
  classical
  rw [S.q_eq_sum_sectors, Finset.mul_sum]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.mul_smul, S.bobSector_idempotent]
  · intro d _ hdc
    rw [Matrix.mul_smul, S.bobSector_mul_eq_zero (Ne.symm hdc)]
    simp
  · simp

theorem alice_off_mirror_block_eq_zero (S : QuantumStrategy)
    (c d : S.SpectralLabel) (hd : d ≠ SpectralLabel.neg S c) :
    S.aliceSector d * S.r * S.aliceSector c = 0 := by
  let X := S.aliceSector d * S.r * S.aliceSector c
  let ad : ℂ := ((2 * d.1 : ℝ) : ℂ)
  let ac : ℂ := ((2 * c.1 : ℝ) : ℂ)
  have hterm1 :
      S.aliceSector d * (S.p * S.r) * S.aliceSector c = ad • X := by
    calc
      _ = (S.aliceSector d * S.p) * S.r * S.aliceSector c := by
        noncomm_ring
      _ = (ad • S.aliceSector d) * S.r * S.aliceSector c := by
        rw [S.aliceSector_mul_p]
      _ = ad • X := by
        simp [X, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hterm2 :
      S.aliceSector d * (S.r * S.p) * S.aliceSector c = ac • X := by
    calc
      _ = S.aliceSector d * S.r * (S.p * S.aliceSector c) := by
        noncomm_ring
      _ = S.aliceSector d * S.r * (ac • S.aliceSector c) := by
        rw [S.p_mul_aliceSector]
      _ = ac • X := by
        simp [X, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hblock : ad • X + ac • X = 0 := by
    rw [← hterm1, ← hterm2]
    calc
      _ = S.aliceSector d * (S.p * S.r + S.r * S.p) *
          S.aliceSector c := by noncomm_ring
      _ = 0 := by rw [S.p_mul_r_add_r_mul_p]; simp
  have hdc : d.1 + c.1 ≠ 0 := by
    intro hzero
    apply hd
    apply Subtype.ext
    change d.1 = -c.1
    linarith
  have hcoefR : 2 * (d.1 + c.1) ≠ (0 : ℝ) :=
    mul_ne_zero (by norm_num) hdc
  have hcoef : ((2 * (d.1 + c.1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hcoefR
  apply Matrix.ext
  intro i j
  have hentry := congrArg (fun M => M i j) hblock
  have hzero : ((2 * (d.1 + c.1) : ℝ) : ℂ) * X i j = 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at hentry
    dsimp [ad, ac] at hentry
    calc
      _ = ad * X i j + ac * X i j := by
        dsimp [ad, ac]
        push_cast
        ring
      _ = 0 := hentry
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

theorem bob_off_mirror_block_eq_zero (S : QuantumStrategy)
    (c d : S.SpectralLabel) (hd : d ≠ SpectralLabel.neg S c) :
    S.bobSector d * S.tau * S.bobSector c = 0 := by
  let X := S.bobSector d * S.tau * S.bobSector c
  let ad : ℂ := ((2 * d.1 : ℝ) : ℂ)
  let ac : ℂ := ((2 * c.1 : ℝ) : ℂ)
  have hterm1 :
      S.bobSector d * (S.q * S.tau) * S.bobSector c = ad • X := by
    calc
      _ = (S.bobSector d * S.q) * S.tau * S.bobSector c := by
        noncomm_ring
      _ = (ad • S.bobSector d) * S.tau * S.bobSector c := by
        rw [S.bobSector_mul_q]
      _ = ad • X := by
        simp [X, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hterm2 :
      S.bobSector d * (S.tau * S.q) * S.bobSector c = ac • X := by
    calc
      _ = S.bobSector d * S.tau * (S.q * S.bobSector c) := by
        noncomm_ring
      _ = S.bobSector d * S.tau * (ac • S.bobSector c) := by
        rw [S.q_mul_bobSector]
      _ = ac • X := by
        simp [X, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hblock : ad • X + ac • X = 0 := by
    rw [← hterm1, ← hterm2]
    calc
      _ = S.bobSector d * (S.q * S.tau + S.tau * S.q) *
          S.bobSector c := by noncomm_ring
      _ = 0 := by rw [S.q_mul_tau_add_tau_mul_q]; simp
  have hdc : d.1 + c.1 ≠ 0 := by
    intro hzero
    apply hd
    apply Subtype.ext
    change d.1 = -c.1
    linarith
  have hcoefR : 2 * (d.1 + c.1) ≠ (0 : ℝ) :=
    mul_ne_zero (by norm_num) hdc
  have hcoef : ((2 * (d.1 + c.1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hcoefR
  apply Matrix.ext
  intro i j
  have hentry := congrArg (fun M => M i j) hblock
  have hzero : ((2 * (d.1 + c.1) : ℝ) : ℂ) * X i j = 0 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at hentry
    dsimp [ad, ac] at hentry
    calc
      _ = ad * X i j + ac * X i j := by
        dsimp [ad, ac]
        push_cast
        ring
      _ = 0 := hentry
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

/-- The `r` block emitted from sector `c` lies entirely in sector `-c`. -/
theorem alice_mirror_sector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.aliceSector (SpectralLabel.neg S c) * S.r * S.aliceSector c =
      S.r * S.aliceSector c := by
  classical
  symm
  calc
    S.r * S.aliceSector c =
        1 * (S.r * S.aliceSector c) := by simp
    _ = (∑ d : S.SpectralLabel, S.aliceSector d) *
        (S.r * S.aliceSector c) := by rw [S.sum_aliceSector]
    _ = ∑ d : S.SpectralLabel,
        S.aliceSector d * S.r * S.aliceSector c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      noncomm_ring
    _ = S.aliceSector (SpectralLabel.neg S c) * S.r *
        S.aliceSector c := by
      rw [Finset.sum_eq_single (SpectralLabel.neg S c)]
      · intro d _ hd
        exact S.alice_off_mirror_block_eq_zero c d hd
      · simp

/-- The `tau` block emitted from sector `c` lies entirely in sector `-c`. -/
theorem bob_mirror_sector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.bobSector (SpectralLabel.neg S c) * S.tau * S.bobSector c =
      S.tau * S.bobSector c := by
  classical
  symm
  calc
    S.tau * S.bobSector c =
        1 * (S.tau * S.bobSector c) := by simp
    _ = (∑ d : S.SpectralLabel, S.bobSector d) *
        (S.tau * S.bobSector c) := by rw [S.sum_bobSector]
    _ = ∑ d : S.SpectralLabel,
        S.bobSector d * S.tau * S.bobSector c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      noncomm_ring
    _ = S.bobSector (SpectralLabel.neg S c) * S.tau *
        S.bobSector c := by
      rw [Finset.sum_eq_single (SpectralLabel.neg S c)]
      · intro d _ hd
        exact S.bob_off_mirror_block_eq_zero c d hd
      · simp

theorem four_mul_s_sq (S : QuantumStrategy) (c : S.SpectralLabel) :
    4 * s c.1 ^ 2 = 4 * (1 - c.1 ^ 2) := by
  have hc := SpectralLabel.value_mem S c
  change c.1 ∈ Set.Icc (-1 : ℝ) 1 at hc
  have hprod : 0 ≤ (c.1 + 1) * (1 - c.1) :=
    mul_nonneg (by linarith [hc.1]) (by linarith [hc.2])
  have harg : 0 ≤ 1 - c.1 ^ 2 := by nlinarith [hprod]
  rw [s, Real.sq_sqrt harg]

theorem r_sq_mul_aliceSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.r * S.r * S.aliceSector c =
      (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.aliceSector c) := by
  let ac : ℂ := ((2 * c.1 : ℝ) : ℂ)
  have hp2 : S.p * S.p * S.aliceSector c =
      (ac * ac) • S.aliceSector c := by
    calc
      _ = S.p * (S.p * S.aliceSector c) := by noncomm_ring
      _ = S.p * (ac • S.aliceSector c) := by rw [S.p_mul_aliceSector]
      _ = ac • (S.p * S.aliceSector c) := by simp [Matrix.mul_smul]
      _ = ac • (ac • S.aliceSector c) := by rw [S.p_mul_aliceSector]
      _ = (ac * ac) • S.aliceSector c := by simp [smul_smul]
  have hpair :
      S.p * S.p * S.aliceSector c + S.r * S.r * S.aliceSector c =
        ((4 : ℂ) • S.aliceSector c) := by
    calc
      _ = (S.p * S.p + S.r * S.r) * S.aliceSector c := by
        noncomm_ring
      _ = (4 • (1 : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)) *
          S.aliceSector c := by rw [S.p_sq_add_r_sq]
      _ = ((4 : ℂ) • (1 : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)) *
          S.aliceSector c := by
        congr 1
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.one_apply, Matrix.smul_apply, hij]
      _ = (4 : ℂ) • S.aliceSector c := by
        simp [Matrix.smul_mul]
  rw [hp2] at hpair
  calc
    S.r * S.r * S.aliceSector c =
        (4 : ℂ) • S.aliceSector c -
          (ac * ac) • S.aliceSector c := eq_sub_of_add_eq' hpair
    _ = (((4 * (1 - c.1 ^ 2) : ℝ) : ℂ) • S.aliceSector c) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      dsimp [ac]
      push_cast
      ring
    _ = (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.aliceSector c) := by
      rw [S.four_mul_s_sq]

theorem tau_sq_mul_bobSector (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.tau * S.tau * S.bobSector c =
      (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.bobSector c) := by
  let ac : ℂ := ((2 * c.1 : ℝ) : ℂ)
  have hq2 : S.q * S.q * S.bobSector c =
      (ac * ac) • S.bobSector c := by
    calc
      _ = S.q * (S.q * S.bobSector c) := by noncomm_ring
      _ = S.q * (ac • S.bobSector c) := by rw [S.q_mul_bobSector]
      _ = ac • (S.q * S.bobSector c) := by simp [Matrix.mul_smul]
      _ = ac • (ac • S.bobSector c) := by rw [S.q_mul_bobSector]
      _ = (ac * ac) • S.bobSector c := by simp [smul_smul]
  have hpair :
      S.q * S.q * S.bobSector c + S.tau * S.tau * S.bobSector c =
        ((4 : ℂ) • S.bobSector c) := by
    calc
      _ = (S.q * S.q + S.tau * S.tau) * S.bobSector c := by
        noncomm_ring
      _ = (4 • (1 : Matrix (Fin S.dimB) (Fin S.dimB) ℂ)) *
          S.bobSector c := by rw [S.q_sq_add_tau_sq]
      _ = ((4 : ℂ) • (1 : Matrix (Fin S.dimB) (Fin S.dimB) ℂ)) *
          S.bobSector c := by
        congr 1
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.one_apply, Matrix.smul_apply, hij]
      _ = (4 : ℂ) • S.bobSector c := by
        simp [Matrix.smul_mul]
  rw [hq2] at hpair
  calc
    S.tau * S.tau * S.bobSector c =
        (4 : ℂ) • S.bobSector c -
          (ac * ac) • S.bobSector c := eq_sub_of_add_eq' hpair
    _ = (((4 * (1 - c.1 ^ 2) : ℝ) : ℂ) • S.bobSector c) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      dsimp [ac]
      push_cast
      ring
    _ = (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.bobSector c) := by
      rw [S.four_mul_s_sq]

theorem alice_block_gram (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.r * S.aliceSector c).conjTranspose *
        (S.r * S.aliceSector c) =
      (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.aliceSector c) := by
  calc
    _ = S.aliceSector c * (S.r * S.r * S.aliceSector c) := by
      rw [Matrix.conjTranspose_mul, S.aliceSector_hermitian,
        S.r_hermitian]
      noncomm_ring
    _ = S.aliceSector c *
        (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.aliceSector c) := by
      rw [S.r_sq_mul_aliceSector]
    _ = (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.aliceSector c) := by
      rw [Matrix.mul_smul, S.aliceSector_idempotent]

theorem bob_block_gram (S : QuantumStrategy) (c : S.SpectralLabel) :
    (S.tau * S.bobSector c).conjTranspose *
        (S.tau * S.bobSector c) =
      (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.bobSector c) := by
  calc
    _ = S.bobSector c * (S.tau * S.tau * S.bobSector c) := by
      rw [Matrix.conjTranspose_mul, S.bobSector_hermitian,
        S.tau_hermitian]
      noncomm_ring
    _ = S.bobSector c *
        (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.bobSector c) := by
      rw [S.tau_sq_mul_bobSector]
    _ = (((4 * s c.1 ^ 2 : ℝ) : ℂ) • S.bobSector c) := by
      rw [Matrix.mul_smul, S.bobSector_idempotent]

/-- A product-space Born cross term is the dot product of the two locally
filtered state vectors. -/
theorem bornNumerator_cross_eq_dotProduct (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B D : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator (A.conjTranspose * C) (B.conjTranspose * D) =
      dotProduct
        (star (Matrix.mulVec (S.tensorOperator A B) S.stateVector))
        (Matrix.mulVec (S.tensorOperator C D) S.stateVector) := by
  rw [S.bornNumerator_eq_dotProduct]
  symm
  calc
    _ = dotProduct (star S.stateVector)
        (Matrix.mulVec ((S.tensorOperator A B).conjTranspose)
          (Matrix.mulVec (S.tensorOperator C D) S.stateVector)) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    _ = dotProduct (star S.stateVector)
        (Matrix.mulVec ((S.tensorOperator A B).conjTranspose *
          S.tensorOperator C D) S.stateVector) := by
      rw [Matrix.mulVec_mulVec]
    _ = dotProduct (star S.stateVector)
        (Matrix.mulVec
          (S.tensorOperator (A.conjTranspose * C) (B.conjTranspose * D))
          S.stateVector) := by
      congr 2
      unfold tensorOperator Matrix.kronecker
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

/-- Finite-dimensional Cauchy--Schwarz for arbitrary local filters, stated
in terms of the Born contraction. -/
theorem bornNumerator_cross_re_le (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B D : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    (S.bornNumerator (A.conjTranspose * C)
        (B.conjTranspose * D)).re ≤
      Real.sqrt
        ((S.bornNumerator (A.conjTranspose * A)
            (B.conjTranspose * B)).re *
          (S.bornNumerator (C.conjTranspose * C)
            (D.conjTranspose * D)).re) := by
  let u := Matrix.mulVec (S.tensorOperator A B) S.stateVector
  let v := Matrix.mulVec (S.tensorOperator C D) S.stateVector
  have h := re_dotProduct_star_le_sqrt_mul u v
  rw [← S.bornNumerator_cross_eq_dotProduct A C B D,
    ← S.bornNumerator_cross_eq_dotProduct A A B B,
    ← S.bornNumerator_cross_eq_dotProduct C C D D] at h
  exact h

theorem bornNumerator_re_eq_expectation_mul_norm (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    (S.bornNumerator A B).re = S.expectation A B * S.stateNormSq := by
  unfold expectation
  field_simp [S.stateNormSq_ne_zero]

/-- Cauchy--Schwarz after division by the strictly positive state norm. -/
theorem expectation_cross_le (S : QuantumStrategy)
    (A C : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B D : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.expectation (A.conjTranspose * C) (B.conjTranspose * D) ≤
      Real.sqrt
        (S.expectation (A.conjTranspose * A) (B.conjTranspose * B) *
          S.expectation (C.conjTranspose * C) (D.conjTranspose * D)) := by
  have hcs := S.bornNumerator_cross_re_le A C B D
  rw [S.bornNumerator_re_eq_expectation_mul_norm,
    S.bornNumerator_re_eq_expectation_mul_norm,
    S.bornNumerator_re_eq_expectation_mul_norm] at hcs
  have hA : (A.conjTranspose * A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self A
  have hB : (B.conjTranspose * B).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self B
  have hC : (C.conjTranspose * C).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self C
  have hD : (D.conjTranspose * D).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self D
  have hfirst : 0 ≤
      S.expectation (A.conjTranspose * A) (B.conjTranspose * B) :=
    S.expectation_nonneg_of_posSemidef hA hB
  have hsecond : 0 ≤
      S.expectation (C.conjTranspose * C) (D.conjTranspose * D) :=
    S.expectation_nonneg_of_posSemidef hC hD
  have hsqrt :
      Real.sqrt
          ((S.expectation (A.conjTranspose * A) (B.conjTranspose * B) *
              S.stateNormSq) *
            (S.expectation (C.conjTranspose * C) (D.conjTranspose * D) *
              S.stateNormSq)) =
        S.stateNormSq *
          Real.sqrt
            (S.expectation (A.conjTranspose * A) (B.conjTranspose * B) *
              S.expectation (C.conjTranspose * C)
                (D.conjTranspose * D)) := by
    rw [show
      (S.expectation (A.conjTranspose * A) (B.conjTranspose * B) *
          S.stateNormSq) *
        (S.expectation (C.conjTranspose * C) (D.conjTranspose * D) *
          S.stateNormSq) =
        S.stateNormSq ^ 2 *
          (S.expectation (A.conjTranspose * A) (B.conjTranspose * B) *
            S.expectation (C.conjTranspose * C) (D.conjTranspose * D)) by ring]
    rw [Real.sqrt_mul (sq_nonneg S.stateNormSq),
      Real.sqrt_sq S.stateNormSq_pos'.le]
  rw [hsqrt] at hcs
  nlinarith [S.stateNormSq_pos']

theorem aliceReflection_hermitian (S : QuantumStrategy) (x : Fin 3) :
    (S.aliceReflection x).conjTranspose = S.aliceReflection x := by
  exact (S.alice x).reflection_hermitian

theorem bobReflection_hermitian (S : QuantumStrategy) (y : Fin 3) :
    (S.bobReflection y).conjTranspose = S.bobReflection y := by
  exact (S.bob y).reflection_hermitian

theorem aliceReflection_sq (S : QuantumStrategy) (x : Fin 3) :
    S.aliceReflection x * S.aliceReflection x = 1 := by
  exact (S.alice x).reflection_sq

theorem bobReflection_sq (S : QuantumStrategy) (y : Fin 3) :
    S.bobReflection y * S.bobReflection y = 1 := by
  exact (S.bob y).reflection_sq

/-- One Alice mirror block is bounded by the geometric mean of its two row
masses. -/
theorem alice_block_expectation_le_aux (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.expectation (S.r * S.aliceSector c) (S.bobReflection 2) ≤
      2 * s c.1 * Real.sqrt
        (S.expectation (S.aliceSector c) 1 *
          S.expectation (S.aliceSector (SpectralLabel.neg S c)) 1) := by
  let cm := SpectralLabel.neg S c
  have h := S.expectation_cross_le
    (S.aliceSector cm) (S.r * S.aliceSector c)
    (1 : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) (S.bobReflection 2)
  have hcross :
      (S.aliceSector cm).conjTranspose * (S.r * S.aliceSector c) =
        S.r * S.aliceSector c := by
    rw [S.aliceSector_hermitian]
    calc
      _ = S.aliceSector cm * S.r * S.aliceSector c := by noncomm_ring
      _ = S.r * S.aliceSector c := by
        exact S.alice_mirror_sector c
  have hleft :
      (S.aliceSector cm).conjTranspose * S.aliceSector cm =
        S.aliceSector cm := by
    rw [S.aliceSector_hermitian, S.aliceSector_idempotent]
  have hone :
      (1 : Matrix (Fin S.dimB) (Fin S.dimB) ℂ).conjTranspose * 1 = 1 := by
    simp
  have hb :
      (S.bobReflection 2).conjTranspose * S.bobReflection 2 = 1 := by
    rw [S.bobReflection_hermitian, S.bobReflection_sq]
  rw [hcross, hleft, hone, S.alice_block_gram, hb] at h
  rw [S.expectation_real_smul_left] at h
  have hs : 0 ≤ s c.1 := Real.sqrt_nonneg _
  have hsqrt :
      Real.sqrt
          (S.expectation (S.aliceSector cm) 1 *
            (4 * s c.1 ^ 2 * S.expectation (S.aliceSector c) 1)) =
        2 * s c.1 *
          Real.sqrt
            (S.expectation (S.aliceSector c) 1 *
              S.expectation (S.aliceSector cm) 1) := by
    rw [show
      S.expectation (S.aliceSector cm) 1 *
          (4 * s c.1 ^ 2 * S.expectation (S.aliceSector c) 1) =
        (2 * s c.1) ^ 2 *
          (S.expectation (S.aliceSector c) 1 *
            S.expectation (S.aliceSector cm) 1) by ring]
    rw [Real.sqrt_mul (sq_nonneg (2 * s c.1)),
      Real.sqrt_sq (mul_nonneg (by norm_num) hs)]
  rw [hsqrt] at h
  simpa [cm] using h

/-- One Bob mirror block is bounded by the geometric mean of its two column
masses. -/
theorem bob_block_expectation_le_aux (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.expectation (S.aliceReflection 2) (S.tau * S.bobSector c) ≤
      2 * s c.1 * Real.sqrt
        (S.expectation 1 (S.bobSector c) *
          S.expectation 1 (S.bobSector (SpectralLabel.neg S c))) := by
  let cm := SpectralLabel.neg S c
  have h := S.expectation_cross_le
    (1 : Matrix (Fin S.dimA) (Fin S.dimA) ℂ) (S.aliceReflection 2)
    (S.bobSector cm) (S.tau * S.bobSector c)
  have hcross :
      (S.bobSector cm).conjTranspose * (S.tau * S.bobSector c) =
        S.tau * S.bobSector c := by
    rw [S.bobSector_hermitian]
    calc
      _ = S.bobSector cm * S.tau * S.bobSector c := by noncomm_ring
      _ = S.tau * S.bobSector c := by exact S.bob_mirror_sector c
  have hleft :
      (S.bobSector cm).conjTranspose * S.bobSector cm =
        S.bobSector cm := by
    rw [S.bobSector_hermitian, S.bobSector_idempotent]
  have hone :
      (1 : Matrix (Fin S.dimA) (Fin S.dimA) ℂ).conjTranspose * 1 = 1 := by
    simp
  have ha :
      (S.aliceReflection 2).conjTranspose * S.aliceReflection 2 = 1 := by
    rw [S.aliceReflection_hermitian, S.aliceReflection_sq]
  rw [hcross, hleft, hone, S.bob_block_gram, ha] at h
  rw [S.expectation_real_smul_right] at h
  have hs : 0 ≤ s c.1 := Real.sqrt_nonneg _
  have hsqrt :
      Real.sqrt
          (S.expectation 1 (S.bobSector cm) *
            (4 * s c.1 ^ 2 * S.expectation 1 (S.bobSector c))) =
        2 * s c.1 *
          Real.sqrt
            (S.expectation 1 (S.bobSector c) *
              S.expectation 1 (S.bobSector cm)) := by
    rw [show
      S.expectation 1 (S.bobSector cm) *
          (4 * s c.1 ^ 2 * S.expectation 1 (S.bobSector c)) =
        (2 * s c.1) ^ 2 *
          (S.expectation 1 (S.bobSector c) *
            S.expectation 1 (S.bobSector cm)) by ring]
    rw [Real.sqrt_mul (sq_nonneg (2 * s c.1)),
      Real.sqrt_sq (mul_nonneg (by norm_num) hs)]
  rw [hsqrt] at h
  simpa [cm] using h

/-- The unsymmetrized joint spectral weight of the `p`-sector `c` and
the `q`-sector `c'`. -/
noncomputable def rawSpectralWeight (S : QuantumStrategy)
    (c c' : S.SpectralLabel) : ℝ :=
  S.expectation (S.aliceSector c) (S.bobSector c')

theorem rawSpectralWeight_nonneg (S : QuantumStrategy)
    (c c' : S.SpectralLabel) : 0 ≤ S.rawSpectralWeight c c' := by
  exact S.expectation_nonneg_of_posSemidef
    (S.aliceSector_posSemidef c) (S.bobSector_posSemidef c')

theorem sum_rawSpectralWeight_right (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    ∑ c' : S.SpectralLabel, S.rawSpectralWeight c c' =
      S.expectation (S.aliceSector c) 1 := by
  unfold rawSpectralWeight
  rw [← S.expectation_sum_right, S.sum_bobSector]

theorem sum_rawSpectralWeight_left (S : QuantumStrategy)
    (c' : S.SpectralLabel) :
    ∑ c : S.SpectralLabel, S.rawSpectralWeight c c' =
      S.expectation 1 (S.bobSector c') := by
  unfold rawSpectralWeight
  rw [← S.expectation_sum_left, S.sum_aliceSector]

theorem rawSpectralWeight_total (S : QuantumStrategy) :
    ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
      S.rawSpectralWeight c c' = 1 := by
  simp_rw [S.sum_rawSpectralWeight_right]
  rw [← S.expectation_sum_left, S.sum_aliceSector]
  exact S.expectation_one_one

/-- The joint spectral distribution before the flipped-transpose
symmetrization. -/
noncomputable def rawSpectralTable (S : QuantumStrategy) : CouplingTable where
  Label := S.SpectralLabel
  label := SpectralLabel.value S
  label_injective := SpectralLabel.value_injective S
  label_mem := SpectralLabel.value_mem S
  weight := S.rawSpectralWeight
  weight_nonneg := S.rawSpectralWeight_nonneg
  totalWeight := S.rawSpectralWeight_total

@[simp] theorem rawSpectralTable_label (S : QuantumStrategy)
    (c : S.SpectralLabel) : S.rawSpectralTable.label c = c.1 := rfl

@[simp] theorem rawSpectralTable_weight (S : QuantumStrategy)
    (c c' : S.SpectralLabel) :
    S.rawSpectralTable.weight c c' = S.rawSpectralWeight c c' := rfl

theorem rawSpectralTable_row (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.rawSpectralTable.row c = S.expectation (S.aliceSector c) 1 := by
  exact S.sum_rawSpectralWeight_right c

theorem rawSpectralTable_column (S : QuantumStrategy) (c : S.SpectralLabel) :
    S.rawSpectralTable.column c = S.expectation 1 (S.bobSector c) := by
  exact S.sum_rawSpectralWeight_left c

/-- The operator Cauchy--Schwarz bound for one Alice mirror block, expressed
in terms of the row masses of the raw spectral table. -/
theorem alice_block_expectation_le (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.expectation (S.r * S.aliceSector c) (S.bobReflection 2) ≤
      2 * s c.1 * Real.sqrt
        (S.rawSpectralTable.row c *
          S.rawSpectralTable.row (SpectralLabel.neg S c)) := by
  rw [S.rawSpectralTable_row, S.rawSpectralTable_row]
  exact S.alice_block_expectation_le_aux c

/-- The operator Cauchy--Schwarz bound for one Bob mirror block, expressed
in terms of the column masses of the raw spectral table. -/
theorem bob_block_expectation_le (S : QuantumStrategy)
    (c : S.SpectralLabel) :
    S.expectation (S.aliceReflection 2) (S.tau * S.bobSector c) ≤
      2 * s c.1 * Real.sqrt
        (S.rawSpectralTable.column c *
          S.rawSpectralTable.column (SpectralLabel.neg S c)) := by
  rw [S.rawSpectralTable_column, S.rawSpectralTable_column]
  exact S.bob_block_expectation_le_aux c

/-- Decomposition of the Alice anticommuting component into spectral
source blocks. -/
theorem r_eq_sum_mul_aliceSector (S : QuantumStrategy) :
    S.r = ∑ c : S.SpectralLabel, S.r * S.aliceSector c := by
  calc
    S.r = S.r * 1 := by simp
    _ = S.r * (∑ c : S.SpectralLabel, S.aliceSector c) := by
      rw [S.sum_aliceSector]
    _ = ∑ c : S.SpectralLabel, S.r * S.aliceSector c := by
      rw [Finset.mul_sum]

/-- Decomposition of the Bob anticommuting component into spectral source
blocks. -/
theorem tau_eq_sum_mul_bobSector (S : QuantumStrategy) :
    S.tau = ∑ c : S.SpectralLabel, S.tau * S.bobSector c := by
  calc
    S.tau = S.tau * 1 := by simp
    _ = S.tau * (∑ c : S.SpectralLabel, S.bobSector c) := by
      rw [S.sum_bobSector]
    _ = ∑ c : S.SpectralLabel, S.tau * S.bobSector c := by
      rw [Finset.mul_sum]

/-- The whole Alice third-setting term is bounded by the sum of its mirror
sector geometric means. -/
theorem alice_third_term_le (S : QuantumStrategy) :
    S.expectation S.r (S.bobReflection 2) ≤
      2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
        (S.rawSpectralTable.row c *
          S.rawSpectralTable.row (SpectralLabel.neg S c)) := by
  rw [S.r_eq_sum_mul_aliceSector, S.expectation_sum_left]
  calc
    ∑ c : S.SpectralLabel,
        S.expectation (S.r * S.aliceSector c) (S.bobReflection 2) ≤
        ∑ c : S.SpectralLabel, 2 * s c.1 * Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c)) := by
      apply Finset.sum_le_sum
      intro c _
      exact S.alice_block_expectation_le c
    _ = 2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- The whole Bob third-setting term is bounded by the sum of its mirror
sector geometric means. -/
theorem bob_third_term_le (S : QuantumStrategy) :
    S.expectation (S.aliceReflection 2) S.tau ≤
      2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
        (S.rawSpectralTable.column c *
          S.rawSpectralTable.column (SpectralLabel.neg S c)) := by
  rw [S.tau_eq_sum_mul_bobSector, S.expectation_sum_right]
  calc
    ∑ c : S.SpectralLabel,
        S.expectation (S.aliceReflection 2) (S.tau * S.bobSector c) ≤
        ∑ c : S.SpectralLabel, 2 * s c.1 * Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c)) := by
      apply Finset.sum_le_sum
      intro c _
      exact S.bob_block_expectation_le c
    _ = 2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- The physical mirror `c ↦ -c` on the raw spectral table. -/
noncomputable def rawSpectralNegation (S : QuantumStrategy) :
    S.rawSpectralTable.Negation where
  neg := SpectralLabel.neg S
  involutive := SpectralLabel.neg_neg S
  label_neg := fun _ ↦ rfl

theorem expectation_p_one_eq_row_moment (S : QuantumStrategy) :
    S.expectation S.p 1 =
      ∑ c : S.SpectralLabel, 2 * c.1 * S.rawSpectralTable.row c := by
  rw [S.p_eq_sum_sectors, S.expectation_sum_left]
  apply Finset.sum_congr rfl
  intro c _
  rw [S.expectation_real_smul_left, S.rawSpectralTable_row]

theorem expectation_one_q_eq_column_moment (S : QuantumStrategy) :
    S.expectation 1 S.q =
      ∑ c : S.SpectralLabel, 2 * c.1 * S.rawSpectralTable.column c := by
  rw [S.q_eq_sum_sectors, S.expectation_sum_right]
  apply Finset.sum_congr rfl
  intro c _
  rw [S.expectation_real_smul_right, S.rawSpectralTable_column]

theorem expectation_p_q_eq_joint_moment (S : QuantumStrategy) :
    S.expectation S.p S.q =
      ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        4 * c.1 * c'.1 * S.rawSpectralWeight c c' := by
  rw [S.p_eq_sum_sectors, S.expectation_sum_left]
  apply Finset.sum_congr rfl
  intro c _
  rw [S.expectation_real_smul_left, S.q_eq_sum_sectors,
    S.expectation_sum_right]
  simp_rw [S.expectation_real_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _
  unfold rawSpectralWeight
  ring

/-- The `d`-weighted part of the raw spectral table is exactly the first
three terms of the reflection-coordinate Bell expression. -/
theorem rawSpectral_linear_exact (S : QuantumStrategy) :
    (∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        d c.1 c'.1 * S.rawSpectralWeight c c') =
      -1 + (S.expectation S.p 1 - S.expectation 1 S.q +
        S.expectation S.p S.q) / 4 := by
  rw [S.expectation_p_one_eq_row_moment,
    S.expectation_one_q_eq_column_moment,
    S.expectation_p_q_eq_joint_moment]
  have hrow :
      (∑ c : S.SpectralLabel, 2 * c.1 * S.rawSpectralTable.row c) =
        ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
          2 * c.1 * S.rawSpectralWeight c c' := by
    apply Finset.sum_congr rfl
    intro c _
    rw [S.rawSpectralTable_row, ← S.sum_rawSpectralWeight_right]
    rw [Finset.mul_sum]
  have hcolumn :
      (∑ c' : S.SpectralLabel, 2 * c'.1 * S.rawSpectralTable.column c') =
        ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
          2 * c'.1 * S.rawSpectralWeight c c' := by
    calc
      _ = ∑ c' : S.SpectralLabel, ∑ c : S.SpectralLabel,
          2 * c'.1 * S.rawSpectralWeight c c' := by
        apply Finset.sum_congr rfl
        intro c' _
        rw [S.rawSpectralTable_column, ← S.sum_rawSpectralWeight_left]
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [hrow, hcolumn]
  let W : ℝ := ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
    S.rawSpectralWeight c c'
  let P : ℝ := ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
    2 * c.1 * S.rawSpectralWeight c c'
  let Q : ℝ := ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
    2 * c'.1 * S.rawSpectralWeight c c'
  let PQ : ℝ := ∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
    4 * c.1 * c'.1 * S.rawSpectralWeight c c'
  have halg :
      (∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        d c.1 c'.1 * S.rawSpectralWeight c c') =
        -W + (P - Q + PQ) / 4 := by
    exact sum_sum_d_algebra (fun c : S.SpectralLabel ↦ c.1)
      (fun c : S.SpectralLabel ↦ c.1) S.rawSpectralWeight
  rw [halg]
  have hW : W = 1 := by exact S.rawSpectralWeight_total
  rw [hW]

/-- The exact reflection-coordinate identity, equation (13) of the paper. -/
theorem four_mul_one_add_value (S : QuantumStrategy) :
    4 * (1 + S.value) =
      S.expectation S.p 1 - S.expectation 1 S.q +
        S.expectation S.p S.q +
        S.expectation S.r (S.bobReflection 2) +
        S.expectation (S.aliceReflection 2) S.tau := by
  unfold value joint aliceMarginal bobMarginal p q r tau aliceReflection bobReflection
  simp only [OrthogonalProjection.reflection, two_nsmul,
    expectation_add_left, expectation_add_right,
    expectation_sub_left, expectation_sub_right, expectation_one_one]
  ring

/-- The Bell value is the raw spectral table's linear term plus one quarter
of the two third-setting reflection terms. -/
theorem value_eq_raw_linear_add_thirds (S : QuantumStrategy) :
    S.value =
      (∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        d c.1 c'.1 * S.rawSpectralWeight c c') +
      (S.expectation S.r (S.bobReflection 2) +
        S.expectation (S.aliceReflection 2) S.tau) / 4 := by
  have hlinear := S.rawSpectral_linear_exact
  have hbell := S.four_mul_one_add_value
  linarith

/-- Distributing the finite sum identifies the raw mirror correction with
the average of its row and column block sums. -/
theorem raw_mirror_terms_eq (S : QuantumStrategy) :
    (∑ c : S.SpectralLabel, s c.1 *
      (Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c)) +
        Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c))) / 2) =
      ((∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c))) +
        (∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c)))) / 2 := by
  calc
    _ = ∑ c : S.SpectralLabel,
        (s c.1 * Real.sqrt
            (S.rawSpectralTable.row c *
              S.rawSpectralTable.row (SpectralLabel.neg S c)) +
          s c.1 * Real.sqrt
            (S.rawSpectralTable.column c *
              S.rawSpectralTable.column (SpectralLabel.neg S c))) / 2 := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = (∑ c : S.SpectralLabel,
        (s c.1 * Real.sqrt
            (S.rawSpectralTable.row c *
              S.rawSpectralTable.row (SpectralLabel.neg S c)) +
          s c.1 * Real.sqrt
            (S.rawSpectralTable.column c *
              S.rawSpectralTable.column (SpectralLabel.neg S c)))) / 2 := by
      rw [Finset.sum_div]
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- Every finite-dimensional complex quantum strategy is bounded by the
raw mirror-sector score of its spectral coupling table. -/
theorem value_le_raw_mirrorScore (S : QuantumStrategy) :
    S.value ≤ S.rawSpectralTable.mirrorScore S.rawSpectralNegation := by
  rw [S.value_eq_raw_linear_add_thirds]
  unfold CouplingTable.mirrorScore
  change
    (∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        d c.1 c'.1 * S.rawSpectralWeight c c') +
        (S.expectation S.r (S.bobReflection 2) +
          S.expectation (S.aliceReflection 2) S.tau) / 4 ≤
      (∑ c : S.SpectralLabel, ∑ c' : S.SpectralLabel,
        d c.1 c'.1 * S.rawSpectralWeight c c') +
        ∑ c : S.SpectralLabel, s c.1 *
          (Real.sqrt
              (S.rawSpectralTable.row c *
                S.rawSpectralTable.row (SpectralLabel.neg S c)) +
            Real.sqrt
              (S.rawSpectralTable.column c *
                S.rawSpectralTable.column (SpectralLabel.neg S c))) / 2
  refine add_le_add (le_refl _) ?_
  calc
    (S.expectation S.r (S.bobReflection 2) +
        S.expectation (S.aliceReflection 2) S.tau) / 4 ≤
      ((2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c))) +
        2 * ∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c))) / 4 := by
      apply div_le_div_of_nonneg_right
      · exact add_le_add S.alice_third_term_le S.bob_third_term_le
      · norm_num
    _ = ((∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.row c *
            S.rawSpectralTable.row (SpectralLabel.neg S c))) +
        (∑ c : S.SpectralLabel, s c.1 * Real.sqrt
          (S.rawSpectralTable.column c *
            S.rawSpectralTable.column (SpectralLabel.neg S c)))) / 2 := by
      ring
    _ = _ := by rw [← S.raw_mirror_terms_eq]

/-- Operator-to-table reduction: every finite-dimensional
complex strategy admits a coupling table whose score dominates its Bell
value.  The witness is the flipped-transpose symmetrization of the
joint spectral table. -/
theorem tableBound (S : QuantumStrategy) :
    ∃ θ : CouplingTable, S.value ≤ θ.score := by
  refine ⟨S.rawSpectralTable.symmetrize S.rawSpectralNegation, ?_⟩
  exact S.value_le_raw_mirrorScore.trans
    (S.rawSpectralTable.mirrorScore_le_symmetrize_score
      S.rawSpectralNegation)

end QuantumStrategy

namespace SchmidtStrategy

/-- The Born numerator of a diagonal Schmidt state as a two-index sum. -/
theorem bornNumerator_eq_sum (S : SchmidtStrategy)
    (A B : Matrix (Fin S.dim) (Fin S.dim) ℂ) :
    S.toQuantumStrategy.bornNumerator A B =
      ∑ i : Fin S.dim, ∑ k : Fin S.dim,
        (S.amplitude i : ℂ) * A i k * B i k * (S.amplitude k : ℂ) := by
  classical
  unfold QuantumStrategy.bornNumerator
  change
    (∑ i : Fin S.dim, ∑ j : Fin S.dim,
      ∑ k : Fin S.dim, ∑ l : Fin S.dim,
        star (S.state i j) * A i k * B j l * S.state k l) = _
  simp_rw [state, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_eq_single k]
    · simp [Complex.conj_ofReal]
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- On a Schmidt-diagonal state, exchanging the two local operators leaves
the scalar expectation unchanged. -/
theorem expectation_swap (S : SchmidtStrategy)
    (A B : Matrix (Fin S.dim) (Fin S.dim) ℂ) :
    S.toQuantumStrategy.expectation A B =
      S.toQuantumStrategy.expectation B A := by
  unfold QuantumStrategy.expectation
  rw [S.bornNumerator_eq_sum, S.bornNumerator_eq_sum]
  have h :
      (∑ i : Fin S.dim, ∑ k : Fin S.dim,
        (S.amplitude i : ℂ) * A i k * B i k * (S.amplitude k : ℂ)) =
      ∑ i : Fin S.dim, ∑ k : Fin S.dim,
        (S.amplitude i : ℂ) * B i k * A i k * (S.amplitude k : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h]

/-- Party exchange followed by flipping every binary outcome. -/
def flipSwap (S : SchmidtStrategy) : SchmidtStrategy where
  dim := S.dim
  dim_pos := S.dim_pos
  amplitude := S.amplitude
  amplitude_nonneg := S.amplitude_nonneg
  normSq_pos := S.normSq_pos
  alice x := (S.bob x).complement
  bob y := (S.alice y).complement

@[simp] theorem flipSwap_amplitude (S : SchmidtStrategy) :
    S.flipSwap.amplitude = S.amplitude := rfl

@[simp] theorem flipSwap_state (S : SchmidtStrategy) :
    S.flipSwap.state = S.state := rfl

theorem flipSwap_expectation (S : SchmidtStrategy)
    (A B : Matrix (Fin S.dim) (Fin S.dim) ℂ) :
    S.flipSwap.toQuantumStrategy.expectation A B =
      S.toQuantumStrategy.expectation A B := by
  unfold QuantumStrategy.expectation QuantumStrategy.stateNormSq
  change
    ((S.toQuantumStrategy.bornNumerator A B).re /
        S.toQuantumStrategy.stateNormSq) = _
  rfl

end SchmidtStrategy
end I3322
