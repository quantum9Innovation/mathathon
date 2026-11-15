import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerTrig
import HierarchicalAbsoluteSpectral.PolynomialDegreeLowerBernsteinOddPart

/-!
The interior Bernstein bound for a real polynomial. The central estimate is
proved by Chebyshev interpolation, then extended to all degrees by odd
projection and localized to the middle half of the interval by affine
composition.
-/

namespace HierarchicalAbsoluteSpectral

open Polynomial Set

/-- The central Bernstein inequality for a real polynomial bounded by `M`
on the unit interval. -/
theorem polynomial_central_bernstein (p : ℝ[X]) (M : ℝ)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M) :
    |p.derivative.eval 0| ≤ p.natDegree * M :=
  central_derivative_bound_of_odd central_odd_degree_derivative_le p M hp

/-- A real polynomial bounded by `M` on `[-1,1]` has derivative bounded by
`2 * natDegree * M` on `[-1/2,1/2]`. -/
theorem polynomial_interior_bernstein (p : ℝ[X]) (M x : ℝ)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M)
    (hx : |x| ≤ 1 / 2) :
    |p.derivative.eval x| ≤ 2 * p.natDegree * M :=
  interior_derivative_bound_of_central polynomial_central_bernstein p M x hp hx

end HierarchicalAbsoluteSpectral
