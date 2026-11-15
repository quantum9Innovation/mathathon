import HierarchicalAbsoluteSpectral.DCTProgram
import HierarchicalAbsoluteSpectral.DyadicDegree

/-!
The complete finite coefficient preparation of Lemma 4, for dyadic size n.
It constructs the root, node powers, samples, and DCT coefficients using
the admissible exact-arithmetic instructions. The associated polynomial
is exactly the interpolant whose uniform error was proved analytically.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
open Polynomial Polynomial.Chebyshev Set

def inverseRootCoefficientProgram (s : ℕ) (η : ℝ) : ArithmeticProgram (Fin (2^s) → ℝ) := do
  let w ← dyadicRootProgram s
  let w2 ← complexMul w w
  let nodes ← powerTableProgram (2^s) w2 w
  let values ← tabulate (2^s) (fun j => inverseRootValueProgram η (nodes j).re)
  dctProgram s w values

theorem dyadic_node_power (s j : ℕ) :
    ((dyadicRoot s)*((dyadicRoot s)*(dyadicRoot s))^j).re = dyadicNode s j := by
  rw [← pow_two, ← pow_mul, ← pow_succ']
  rfl

theorem inverseRootCoefficientProgram_eval (s : ℕ) (η : ℝ) (k : Fin (2^s)) :
    (inverseRootCoefficientProgram s η).eval k =
      dyadicDCTCoefficient s (fun j => inverseRootValue η (dyadicNode s j)) k := by
  simp only [inverseRootCoefficientProgram, eval_bind, dyadicRootProgram_eval, eval_complexMul,
    eval_tabulate, inverseRootValueProgram_eval, powerTableProgram_eval, dyadic_node_power]
  exact dctProgram_eval s _ k

theorem inverseRootCoefficientProgram_work (s : ℕ) (η : ℝ) :
    (inverseRootCoefficientProgram s η).work = fftWork (s+2)+3*s+11+14*2^s := by
  simp only [inverseRootCoefficientProgram, work_bind, dyadicRootProgram_work, work_complexMul,
    powerTableProgram_work, work_tabulate, inverseRootValueProgram_work, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, dctProgram_work]
  ring

theorem inverseRootCoefficientProgram_work_bound (s : ℕ) (η : ℝ) :
    (inverseRootCoefficientProgram s η).work ≤ 64*(s+3)*2^s := by
  rw [inverseRootCoefficientProgram_work]
  have h := fftWork_exact (s+2)
  rw [pow_add] at h
  norm_num at h
  have hn : 1 ≤ 2^s := one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
  nlinarith

theorem inverseRootCoefficientProgram_admissible (s : ℕ) (η : ℝ) (hη : 0 < η) :
    (inverseRootCoefficientProgram s η).admissible := by
  simp only [inverseRootCoefficientProgram, admissible_bind, dyadicRootProgram_admissible,
    admissible_complexMul, powerTableProgram_admissible, admissible_tabulate,
    inverseRootValueProgram_admissible _ _ hη, dctProgram_admissible, and_true,
    implies_true]

def polynomialFromChebyshevCoefficients (s : ℕ) (a : Fin (2^s) → ℝ) : ℝ[X] :=
  ∑ k : Fin (2^s), a k • T ℝ (k.val : ℤ)

theorem inverseRootCoefficientProgram_polynomial (s : ℕ) (η : ℝ) :
    polynomialFromChebyshevCoefficients s (inverseRootCoefficientProgram s η).eval =
      inverseRootInterpolant s η := by
  simp only [polynomialFromChebyshevCoefficients, inverseRootCoefficientProgram_eval,
    inverseRootInterpolant_eq_DCT, dyadicDCT_apply]

/-- The polynomial accuracy, degree and construction count refer to the same
executed program. This is Lemma 4 with an explicit uniform work constant. -/
theorem finite_inverse_root_polynomial (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    ∃ s : ℕ,
      let P := inverseRootCoefficientProgram s η
      let p := polynomialFromChebyshevCoefficients s P.eval
      P.admissible ∧ P.work ≤ 64*(s+3)*2^s ∧ p.degree < (2^s : ℕ) ∧
      (2^s : ℝ) ≤ (17000/η)*Real.log (1/(τ*η)) ∧
      ∀ x ∈ Icc (-1:ℝ) 1, |p.eval x*Real.sqrt (absoluteRootScalar η x)-1| ≤ τ := by
  refine ⟨inverseRootLevel η τ hη hτ, inverseRootCoefficientProgram_admissible _ η hη,
    inverseRootCoefficientProgram_work_bound _ η, ?_,
    inverseRootLevel_degree_bound_simple η τ hη hη' hτ hτ', ?_⟩
  · rw [inverseRootCoefficientProgram_polynomial]
    exact inverseRootInterpolant_degree _ _
  · rw [inverseRootCoefficientProgram_polynomial]
    exact inverseRootInterpolant_relative_error _ η τ hη hη' hτ
      (inverseRootLevel_stops η τ hη hτ)

end
end HierarchicalAbsoluteSpectral
