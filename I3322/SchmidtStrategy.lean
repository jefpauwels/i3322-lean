import I3322.QuantumStrategy
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Canonical Schmidt-form strategies

For the finite-dimensional Bell problem we use the standard canonical
presentation in a Schmidt basis: both local spaces have the same finite
dimension, the state coefficient matrix is diagonal, and its diagonal entries
are nonnegative real amplitudes.  Local changes of basis are absorbed into the
measurement projectors.

`QuantumStrategy` remains the general coefficient-matrix model, while the
normal-form presentation is represented by a separate type.
-/

namespace I3322

/-- A finite-dimensional projective strategy written in a Schmidt basis. -/
structure SchmidtStrategy where
  dim : ℕ
  dim_pos : 0 < dim
  amplitude : Fin dim → ℝ
  amplitude_nonneg : ∀ i, 0 ≤ amplitude i
  normSq_pos : 0 < ∑ i, amplitude i ^ 2
  alice : Fin 3 → OrthogonalProjection dim
  bob : Fin 3 → OrthogonalProjection dim

namespace SchmidtStrategy

open scoped BigOperators

/-- Squared norm of the Schmidt vector. -/
noncomputable def normSq (S : SchmidtStrategy) : ℝ :=
  ∑ i, S.amplitude i ^ 2

theorem normSq_pos' (S : SchmidtStrategy) : 0 < S.normSq :=
  S.normSq_pos

/-- The diagonal coefficient matrix of the Schmidt vector. -/
noncomputable def state (S : SchmidtStrategy) :
    Matrix (Fin S.dim) (Fin S.dim) ℂ :=
  Matrix.diagonal fun i => (S.amplitude i : ℂ)

theorem state_normSq (S : SchmidtStrategy) :
    ∑ i : Fin S.dim, ∑ j : Fin S.dim, Complex.normSq (S.state i j) =
      S.normSq := by
  classical
  unfold state normSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Complex.normSq_apply]
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Forget the displayed Schmidt data and obtain a complex strategy. -/
noncomputable def toQuantumStrategy (S : SchmidtStrategy) : QuantumStrategy where
  dimA := S.dim
  dimB := S.dim
  dimA_pos := S.dim_pos
  dimB_pos := S.dim_pos
  state := S.state
  stateNormSq_pos := by
    rw [S.state_normSq]
    exact S.normSq_pos'
  alice := S.alice
  bob := S.bob

/-- The `I3322` value of a Schmidt-form strategy. -/
noncomputable def value (S : SchmidtStrategy) : ℝ :=
  S.toQuantumStrategy.value

/-- A concrete nonempty witness for the strategy class. -/
noncomputable def trivial : SchmidtStrategy where
  dim := 1
  dim_pos := by omega
  amplitude := fun _ => 1
  amplitude_nonneg := by simp
  normSq_pos := by simp
  alice := fun _ => OrthogonalProjection.zero 1
  bob := fun _ => OrthogonalProjection.zero 1

instance : Nonempty SchmidtStrategy := ⟨trivial⟩

/-- The finite-dimensional quantum supremum in canonical Schmidt form. -/
noncomputable def quantumSupremum : ℝ :=
  sSup (Set.range value)

end SchmidtStrategy
end I3322
