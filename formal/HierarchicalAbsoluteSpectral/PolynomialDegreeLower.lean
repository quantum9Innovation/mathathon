import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerBernstein
import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerCore
import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerScalar

/-!
The manuscript's scoped polynomial degree lower bound. The Bernstein
inequality is proved in the imported modules, rather than assumed here.
The proof below follows the manuscript's maximum/mean-value argument.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Polynomial Set Matrix
open scoped MatrixOrder

/-- Uniform absolute-value inverse congruences need degree proportional
to reciprocal accuracy when their central value is large. -/
theorem polynomial_inverse_congruence_natDegree_lower
    (p : ℝ[X]) (C ε : ℝ) (hCε : 0 < C*ε) (hsmall : C*ε ≤ 1/16)
    (hweighted : ∀ x ∈ Icc (-1 : ℝ) 1, |x| * (p.eval x)^2 ≤ 1)
    (hzero : 1/(C*ε) ≤ (p.eval 0)^2) :
    1/(20*C*ε) ≤ (p.natDegree : ℝ) := by
  have h := polynomial_natDegree_lower_of_derivative_bound p (C*ε) hCε hsmall
    hweighted hzero (fun M _ hM x hx =>
      polynomial_interior_bernstein p M x hM (abs_le.mpr hx))
  simpa only [mul_assoc] using h

/-- The same lower bound when the central value is derived from the
literal zero-threshold scalar relaxed invariant. -/
theorem polynomial_inverse_congruence_natDegree_lower_of_zero_threshold
    (p : ℝ[X]) (C ε κ : ℝ) (hCε : 0 < C*ε) (hsmall : C*ε ≤ 1/16)
    (hweighted : ∀ x ∈ Icc (-1 : ℝ) 1, |x| * (p.eval x)^2 ≤ 1)
    (hR : IsUnit (((p.eval 0) • (1 : Core 1)).det))
    (hinvariant :
      inverseMetric ((p.eval 0) • (1 : Core 1)) -
        κ • ((0 : Core 1) * (inverseMetric ((p.eval 0) • (1 : Core 1)))⁻¹ * 0) ≤
          (C*ε) • (1 : Core 1)) :
    1/(20*C*ε) ≤ (p.natDegree : ℝ) := by
  apply polynomial_inverse_congruence_natDegree_lower p C ε hCε hsmall hweighted
  exact polynomial_central_square_lower_of_zero_threshold p C ε κ hCε hR hinvariant

/-- An additional sharp-order central estimate obtained by applying the
proved central Chebyshev bound directly to `X*p²`. -/
theorem polynomial_inverse_congruence_natDegree_lower_central
    (p : ℝ[X]) (C ε : ℝ)
    (hweighted : ∀ x ∈ Icc (-1 : ℝ) 1, |x| * (p.eval x)^2 ≤ 1)
    (hzero : 1/(C*ε) ≤ (p.eval 0)^2) :
    (1/(C*ε)-1)/2 ≤ (p.natDegree : ℝ) := by
  have hcentral := weighted_square_eval_zero_le_degree p hweighted
  linarith

end
end HierarchicalAbsoluteSpectral
