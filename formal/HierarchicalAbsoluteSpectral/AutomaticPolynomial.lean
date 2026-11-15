import HierarchicalAbsoluteSpectral.DegreeSelection
import HierarchicalAbsoluteSpectral.PolynomialConstruction

/-!
Lemma 4 as one algorithm on the paper's scalar input parameters. Its
output is a dyadic size and a materialized table of Chebyshev coefficients.
Degree selection, scalar roots, samples, and the Fourier transform all
belong to the same operational program and operation count.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
open Polynomial Set

def automaticInverseRootProgram (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    ArithmeticProgram (Σ s : ℕ, Fin (2^s) → ℝ) := do
  let s ← degreeSelectionProgram η τ hη hτ
  let a ← inverseRootCoefficientProgram s η
  ArithmeticProgram.pure ⟨s,a⟩

theorem automaticInverseRootProgram_eval (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    (automaticInverseRootProgram η τ hη hτ).eval =
      ⟨inverseRootLevel η τ hη hτ,
        (inverseRootCoefficientProgram (inverseRootLevel η τ hη hτ) η).eval⟩ := by
  simp only [automaticInverseRootProgram, eval_bind, eval_pure]
  rw [(degreeSelectionProgram_specification η τ hη hτ).1]

theorem automaticInverseRootProgram_work (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    (automaticInverseRootProgram η τ hη hτ).work =
      2*inverseRootLevel η τ hη hτ+8+
        (inverseRootCoefficientProgram (inverseRootLevel η τ hη hτ) η).work := by
  simp only [automaticInverseRootProgram, work_bind, work_pure, add_zero,
    (degreeSelectionProgram_specification η τ hη hτ).2.1]
  rw [(degreeSelectionProgram_specification η τ hη hτ).1]

theorem automaticInverseRootProgram_polynomial (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    polynomialFromChebyshevCoefficients (automaticInverseRootProgram η τ hη hτ).eval.1
      (automaticInverseRootProgram η τ hη hτ).eval.2 = inverseRootPolynomial η τ := by
  rw [automaticInverseRootProgram_eval, inverseRootCoefficientProgram_polynomial,
    inverseRootPolynomial_eq η τ hη hτ]

theorem automaticInverseRootProgram_work_bound (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    (automaticInverseRootProgram η τ hη hτ).work ≤
      80*(inverseRootLevel η τ hη hτ+3)*2^(inverseRootLevel η τ hη hτ) := by
  rw [automaticInverseRootProgram_work]
  have hc := inverseRootCoefficientProgram_work_bound (inverseRootLevel η τ hη hτ) η
  have hn : 1 ≤ 2^(inverseRootLevel η τ hη hτ) := one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
  nlinarith

theorem automaticInverseRootProgram_admissible (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    (automaticInverseRootProgram η τ hη hτ).admissible := by
  simp only [automaticInverseRootProgram, admissible_bind, admissible_pure, and_true,
    inverseRootCoefficientProgram_admissible _ _ hη, and_true]
  exact (degreeSelectionProgram_specification η τ hη hτ).2.2

/-- Lemma 4, with inputs, actual output polynomial, error, degree and total
construction count stated together. `n=2^s`, so the count is O(n log n). -/
theorem inverse_root_polynomial_algorithm (η τ : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1/8) (hτ : 0 < τ) (hτ' : τ < 1/4) :
    let P := automaticInverseRootProgram η τ hη hτ
    let s := P.eval.1
    let p := polynomialFromChebyshevCoefficients s P.eval.2
    P.admissible ∧ P.work ≤ 80*(s+3)*2^s ∧ p.degree < (2^s : ℕ) ∧
      (2^s : ℝ) ≤ (17000/η)*Real.log (1/(τ*η)) ∧
      ∀ x ∈ Icc (-1:ℝ) 1, |p.eval x*Real.sqrt (absoluteRootScalar η x)-1| ≤ τ := by
  dsimp only
  rw [automaticInverseRootProgram_eval, inverseRootCoefficientProgram_polynomial]
  refine ⟨automaticInverseRootProgram_admissible η τ hη hτ,
    automaticInverseRootProgram_work_bound η τ hη hτ, inverseRootInterpolant_degree _ _,
    inverseRootLevel_degree_bound_simple η τ hη hη' hτ hτ', ?_⟩
  exact inverseRootInterpolant_relative_error _ η τ hη hη' hτ
    (inverseRootLevel_stops η τ hη hτ)

end
end HierarchicalAbsoluteSpectral
