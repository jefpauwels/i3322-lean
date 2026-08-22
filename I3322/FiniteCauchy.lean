import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.BigOperators

/-! # Finite-vector Cauchy--Schwarz in Born-contraction form -/

namespace I3322

/-- Cauchy--Schwarz for finite complex vectors, stated with the
`dotProduct (star u) v` convention used by the Born contraction. -/
theorem re_dotProduct_star_le_sqrt_mul {ι : Type*} [Fintype ι]
    (u v : ι → ℂ) :
    (dotProduct (star u) v).re ≤
      Real.sqrt ((dotProduct (star u) u).re *
        (dotProduct (star v) v).re) := by
  let U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  let V : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hcs := re_inner_le_norm (𝕜 := ℂ) U V
  have hinner : inner ℂ U V = dotProduct (star u) v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hU : (dotProduct (star u) u).re = ‖U‖ ^ 2 := by
    have hself : inner ℂ U U = dotProduct (star u) u := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    calc
      _ = (inner ℂ U U).re := congrArg Complex.re hself.symm
      _ = ‖U‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) U).symm
  have hV : (dotProduct (star v) v).re = ‖V‖ ^ 2 := by
    have hself : inner ℂ V V = dotProduct (star v) v := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    calc
      _ = (inner ℂ V V).re := congrArg Complex.re hself.symm
      _ = ‖V‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) V).symm
  rw [hinner] at hcs
  rw [hU, hV,
    show ‖U‖ ^ 2 * ‖V‖ ^ 2 = (‖U‖ * ‖V‖) ^ 2 by ring,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact hcs

end I3322
