import HierarchicalAbsoluteSpectral.DyadicDegree
import HierarchicalAbsoluteSpectral.FiniteRefinement

/-!
The finite refinement with its scalar polynomial fully instantiated. This
theorem has no polynomial-approximation or metric-closeness oracle. Its
inputs are the previous invariant and the two fine-proxy error inequalities.
Arithmetic operation bounds are a separate obligation.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped MatrixOrder
variable {k : ℕ}

def refinementPolynomial (ε h B : ℝ) : ℝ[X] :=
  inverseRootPolynomial (8*ε) (refinementTolerance h B)

def finiteRefinementFactor (R Kj : Core k) (ε h B : ℝ) : Core k :=
  refinedInverseFactor R Kj ε (refinementPolynomial ε h B)

theorem refinementPolynomial_approximation (ε h B : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1/1024) (hh : 0 < h) (hB : 0 ≤ B)
    (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(refinementPolynomial ε h B).eval x * Real.sqrt (absoluteRootScalar (8*ε) x)-1| ≤
      refinementTolerance h B := by
  apply inverseRootPolynomial_relative_error (8*ε) (refinementTolerance h B)
    (by positivity) (by linarith)
  · unfold refinementTolerance
    positivity
  · exact hx

theorem refinementPolynomial_degree (ε h B : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1/1024) (hh : 0 < h) (hh' : h ≤ 1/64) (hB : 0 ≤ B) :
    ∃ n : ℕ, (refinementPolynomial ε h B).degree < n ∧
      (n : ℝ) ≤ (17000/(8*ε))*Real.log (1/(refinementTolerance h B*(8*ε))) := by
  have ht := refinement_tolerance_bounds h B hh hh' hB
  exact inverseRootPolynomial_degree (8*ε) (refinementTolerance h B)
    (by positivity) (by linarith) ht.1 (by linarith [ht.2.2.1])

/-- The actual finite factor satisfies all of the refinement invariant (9),
including the 55h margins. The polynomial and its uniform approximation
are constructed by `inverseRootLevel` and `inverseRootInterpolant`.
-/
theorem constructed_finite_refinement
    (R K Kj D : Core k) (κ C B h H ε : ℝ)
    (hR : IsUnit R.det) (hD : D.PosDef) (hK : Kᵀ = K) (hKj : Kjᵀ = Kj)
    (hκ : 0 ≤ κ) (hκ' : κ ≤ 5) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hH : 0 < H) (hε : 0 < ε) (hε' : ε ≤ 1/1024)
    (hscale : h = ε*H)
    (hfloor : (8*H) • D ≤ inverseMetric R)
    (hbound : inverseMetric R ≤ B • D)
    (hKlo : -inverseMetric R ≤ K) (hKup : K ≤ inverseMetric R)
    (hlow : -((8*h) • D) ≤ Kj-K) (hupper : Kj-K ≤ (8*h) • D)
    (hinvariant : inverseMetric R - κ • (K * (inverseMetric R)⁻¹ * K) ≤ (C*H) • D) :
    IsUnit (finiteRefinementFactor R Kj ε h B).det ∧
    (8*h) • D ≤ inverseMetric (finiteRefinementFactor R Kj ε h B) ∧
    inverseMetric (finiteRefinementFactor R Kj ε h B) ≤ (2*B) • D ∧
    (55*h) • D ≤ inverseMetric (finiteRefinementFactor R Kj ε h B)-K ∧
    (55*h) • D ≤ inverseMetric (finiteRefinementFactor R Kj ε h B)+K ∧
    inverseMetric (finiteRefinementFactor R Kj ε h B) - (5:ℝ) •
      (K * (inverseMetric (finiteRefinementFactor R Kj ε h B))⁻¹ * K) ≤
        (100*(C+1)*h) • D := by
  exact finite_refinement_invariant R K Kj D κ C B h H ε hR hD hK hKj
    hκ hκ' hC hB hh hh' hH hε hε' hscale hfloor hbound hKlo hKup hlow hupper hinvariant
    (refinementPolynomial ε h B) (refinementPolynomial_approximation ε h B hε hε' hh hB)

end
end HierarchicalAbsoluteSpectral
