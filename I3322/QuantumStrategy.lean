import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.NoncommRing

/-!
# Finite-dimensional quantum strategies for `I3322`

The state is a (not necessarily normalized) vector in a finite tensor-product
basis, represented by its coefficient matrix.  A binary outcome-`1` effect is
an orthogonal projection: a Hermitian idempotent complex matrix.  Expectations
are finite Born-rule contractions divided by the squared norm of the state.
-/

namespace I3322

/-- A finite-dimensional orthogonal projection, in a fixed basis. -/
structure OrthogonalProjection (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  hermitian : matrix.conjTranspose = matrix
  idempotent : matrix * matrix = matrix

namespace OrthogonalProjection

/-- The zero projection. -/
def zero (n : ℕ) : OrthogonalProjection n where
  matrix := 0
  hermitian := by simp
  idempotent := by simp

/-- The identity projection. -/
def one (n : ℕ) : OrthogonalProjection n where
  matrix := 1
  hermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  idempotent := by simp

@[simp] theorem zero_matrix (n : ℕ) : (zero n).matrix = 0 := rfl
@[simp] theorem one_matrix (n : ℕ) : (one n).matrix = 1 := rfl

/-- Change the orthonormal basis of a projection by a unitary matrix. -/
noncomputable def conjugate {n : ℕ} (P : OrthogonalProjection n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : OrthogonalProjection n where
  matrix := U.val.conjTranspose * P.matrix * U.val
  hermitian := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, P.hermitian]
    simp [mul_assoc]
  idempotent := by
    have hU : U.val * U.val.conjTranspose = 1 := U.2.2
    calc
      (U.val.conjTranspose * P.matrix * U.val) *
          (U.val.conjTranspose * P.matrix * U.val) =
          U.val.conjTranspose * P.matrix *
            (U.val * U.val.conjTranspose) * P.matrix * U.val := by
              noncomm_ring
      _ = U.val.conjTranspose * (P.matrix * P.matrix) * U.val := by
        rw [hU]
        simp [mul_assoc]
      _ = U.val.conjTranspose * P.matrix * U.val := by rw [P.idempotent]

@[simp] theorem conjugate_matrix {n : ℕ} (P : OrthogonalProjection n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (P.conjugate U).matrix = U.val.conjTranspose * P.matrix * U.val := rfl

end OrthogonalProjection

/--
A finite-dimensional bipartite strategy with three binary projective
measurements per party.  The local dimensions may differ.
-/
structure QuantumStrategy where
  dimA : ℕ
  dimB : ℕ
  dimA_pos : 0 < dimA
  dimB_pos : 0 < dimB
  state : Matrix (Fin dimA) (Fin dimB) ℂ
  stateNormSq_pos :
    0 < ∑ i : Fin dimA, ∑ j : Fin dimB, Complex.normSq (state i j)
  alice : Fin 3 → OrthogonalProjection dimA
  bob : Fin 3 → OrthogonalProjection dimB

namespace QuantumStrategy

/-- Squared Hilbert-space norm of the (possibly unnormalized) state. -/
noncomputable def stateNormSq (S : QuantumStrategy) : ℝ :=
  ∑ i : Fin S.dimA, ∑ j : Fin S.dimB, Complex.normSq (S.state i j)

theorem stateNormSq_pos' (S : QuantumStrategy) : 0 < S.stateNormSq :=
  S.stateNormSq_pos

theorem stateNormSq_ne_zero (S : QuantumStrategy) : S.stateNormSq ≠ 0 :=
  ne_of_gt S.stateNormSq_pos'

/-- The unnormalized complex Born contraction `⟨ψ| A ⊗ B |ψ⟩`. -/
noncomputable def bornNumerator (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) : ℂ :=
  ∑ i : Fin S.dimA, ∑ j : Fin S.dimB,
    ∑ k : Fin S.dimA, ∑ l : Fin S.dimB,
      star (S.state i j) * A i k * B j l * S.state k l

/-- The same Born contraction in the single-space trace notation used in the
operator reduction.  The transpose on Bob's matrix comes from the
coefficient-matrix convention for `state`. -/
theorem bornNumerator_eq_trace (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) :
    S.bornNumerator A B =
      Matrix.trace (A * S.state * B.transpose * S.state.conjTranspose) := by
  classical
  simp only [bornNumerator, Matrix.trace, Matrix.mul_apply,
    Matrix.diag_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The real normalized Born expectation of two local operators. -/
noncomputable def expectation (S : QuantumStrategy)
    (A : Matrix (Fin S.dimA) (Fin S.dimA) ℂ)
    (B : Matrix (Fin S.dimB) (Fin S.dimB) ℂ) : ℝ :=
  (S.bornNumerator A B).re / S.stateNormSq

/-- Joint probability `P(11|xy)`. -/
noncomputable def joint (S : QuantumStrategy) (x y : Fin 3) : ℝ :=
  S.expectation (S.alice x).matrix (S.bob y).matrix

/-- Alice's marginal probability `P_A(1|x)`. -/
noncomputable def aliceMarginal (S : QuantumStrategy) (x : Fin 3) : ℝ :=
  S.expectation (S.alice x).matrix 1

/-- Bob's marginal probability `P_B(1|y)`. -/
noncomputable def bobMarginal (S : QuantumStrategy) (y : Fin 3) : ℝ :=
  S.expectation 1 (S.bob y).matrix

/--
The `I3322` normalization, with outcome-`1` effects and
zero-based measurement indices.
-/
noncomputable def value (S : QuantumStrategy) : ℝ :=
  -S.aliceMarginal 1 - S.bobMarginal 0 - 2 * S.bobMarginal 1
    + S.joint 0 0 + S.joint 0 1 + S.joint 1 0 + S.joint 1 1
    - S.joint 0 2 + S.joint 1 2 - S.joint 2 0 + S.joint 2 1

/-- A concrete one-dimensional strategy, used to witness nonemptiness of the
set whose supremum defines the finite-dimensional quantum value. -/
noncomputable def trivial : QuantumStrategy where
  dimA := 1
  dimB := 1
  dimA_pos := by omega
  dimB_pos := by omega
  state := fun _ _ => 1
  stateNormSq_pos := by simp [Complex.normSq_apply]
  alice := fun _ => OrthogonalProjection.zero 1
  bob := fun _ => OrthogonalProjection.zero 1

instance : Nonempty QuantumStrategy := ⟨trivial⟩

end QuantumStrategy
end I3322
