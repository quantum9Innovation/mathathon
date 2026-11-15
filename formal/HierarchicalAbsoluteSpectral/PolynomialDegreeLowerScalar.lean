import HierarchicalAbsoluteSpectral.InverseMetric
import Mathlib.Algebra.Polynomial.Basic

/-! At a zero threshold, the one-dimensional relaxed invariant forces a
large central polynomial value. This is the normalized scalar instance
`K=0`, `D=1`, `ε=h/H` of the manuscript's matrix invariant. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix Polynomial
open scoped MatrixOrder

theorem central_square_lower_of_inverse_metric_bound (s δ F : ℝ)
    (hδ : 0 < δ) (hmetric : F*s^2 = 1) (hbound : F ≤ δ) :
    1/δ ≤ s^2 := by
  rw [div_le_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_right hbound (sq_nonneg s)]

/-- A literal one-by-one instance of the zero-threshold relaxed invariant.
Invertibility is the ordinary inverse-factor precondition, not an extra
lower bound on the polynomial value. -/
theorem polynomial_central_square_lower_of_zero_threshold
    (p : ℝ[X]) (C ε κ : ℝ) (hCε : 0 < C*ε)
    (hR : IsUnit (((p.eval 0) • (1 : Core 1)).det))
    (hinvariant :
      inverseMetric ((p.eval 0) • (1 : Core 1)) -
        κ • ((0 : Core 1) * (inverseMetric ((p.eval 0) • (1 : Core 1)))⁻¹ * 0) ≤
          (C*ε) • (1 : Core 1)) :
    1/(C*ε) ≤ (p.eval 0)^2 := by
  let R : Core 1 := (p.eval 0) • (1 : Core 1)
  let F := inverseMetric R
  have hnormalized := congrArg (fun M : Core 1 => M 0 0) (inverseMetric_normalized R hR)
  have hmetric : F 0 0*(p.eval 0)^2 = 1 := by
    simp only [R, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_true] at hnormalized
    dsimp only [F]
    nlinarith only [hnormalized]
  have hrelaxed : F ≤ (C*ε) • (1 : Core 1) := by
    simpa only [Matrix.zero_mul, Matrix.mul_zero, smul_zero, sub_zero] using hinvariant
  have hscalar := quadratic_mono hrelaxed (fun _ : Fin 1 => 1)
  have hbound : F 0 0 ≤ C*ε := by
    simpa [quadratic, Matrix.mulVec, dotProduct] using hscalar
  exact central_square_lower_of_inverse_metric_bound (p.eval 0) (C*ε) (F 0 0)
    hCε hmetric hbound

end
end HierarchicalAbsoluteSpectral
