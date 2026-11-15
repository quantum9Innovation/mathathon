import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
The maximum/mean-value portion of the scoped polynomial degree lower bound.
The interior Bernstein estimate is an explicit hypothesis of these lemmas.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

open Polynomial Set

/-- A large attained value, the weighted-square constraint, and the interior
Bernstein estimate force a proportional polynomial degree. -/
theorem polynomial_square_le_twenty_natDegree_of_central_derivative_bound
    (p : ℝ[X]) (M x₀ : ℝ)
    (hM : M = |p.eval x₀|) (hMsq : 16 ≤ M ^ 2)
    (hx₀ : x₀ ∈ Icc (-1 : ℝ) 1)
    (hweighted : ∀ x ∈ Icc (-1 : ℝ) 1, |x| * (p.eval x) ^ 2 ≤ 1)
    (hderiv : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      |p.derivative.eval x| ≤ 2 * (p.natDegree : ℝ) * M) :
    M ^ 2 ≤ 20 * (p.natDegree : ℝ) := by
  have hMnonneg : 0 ≤ M := by rw [hM]; exact abs_nonneg _
  have hMpos : 0 < M := by nlinarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hMsqpos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hrecip : 1 / M ^ 2 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hMsqpos).mpr
    nlinarith
  have hx₀small : |x₀| ≤ 1 / M ^ 2 := by
    apply (le_div_iff₀ hMsqpos).mpr
    have hw := hweighted x₀ hx₀
    simpa only [hM, sq_abs] using hw
  have hx₀central : x₀ ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    exact abs_le.mp (hx₀small.trans hrecip)
  let x₁ : ℝ := 4 / M ^ 2
  have hx₁nonneg : 0 ≤ x₁ := by dsimp [x₁]; positivity
  have hx₁small : x₁ ≤ (1 / 2 : ℝ) := by
    dsimp [x₁]
    apply (div_le_iff₀ hMsqpos).mpr
    nlinarith
  have hx₁central : x₁ ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    constructor <;> linarith
  have hx₁ : x₁ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx₁central.1, hx₁central.2]
  have hvalue : |p.eval x₁| ≤ M / 2 := by
    have hw := hweighted x₁ hx₁
    rw [abs_of_nonneg hx₁nonneg] at hw
    have hscaled := mul_le_mul_of_nonneg_right hw hMsqpos.le
    have hcancel : x₁ * (p.eval x₁) ^ 2 * M ^ 2 =
        4 * (p.eval x₁) ^ 2 := by
      dsimp [x₁]
      field_simp
    rw [hcancel, one_mul] at hscaled
    nlinarith [sq_abs (p.eval x₁), abs_nonneg (p.eval x₁)]
  have hseparation : M / 2 ≤ |p.eval x₁ - p.eval x₀| := by
    have htriangle := abs_add_le (p.eval x₀ - p.eval x₁) (p.eval x₁)
    rw [sub_add_cancel, ← hM, abs_sub_comm (p.eval x₀) (p.eval x₁)] at htriangle
    linarith
  have hdist : |x₁ - x₀| ≤ 5 / M ^ 2 := by
    have htriangle := abs_add_le x₁ (-x₀)
    rw [abs_neg, abs_of_nonneg hx₁nonneg] at htriangle
    change |x₁ - x₀| ≤ 5 / M ^ 2
    calc
      |x₁ - x₀| ≤ x₁ + |x₀| := by simpa only [sub_eq_add_neg] using htriangle
      _ ≤ 4 / M ^ 2 + 1 / M ^ 2 := add_le_add (le_refl _) hx₀small
      _ = 5 / M ^ 2 := by ring
  have hmv : |p.eval x₁ - p.eval x₀| ≤
      (2 * (p.natDegree : ℝ) * M) * |x₁ - x₀| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x (_ : x ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) =>
          p.hasDerivWithinAt x (Icc (-(1 / 2) : ℝ) (1 / 2)))
        (fun x hx => by simpa only [Real.norm_eq_abs] using hderiv x hx)
        (convex_Icc (-(1 / 2) : ℝ) (1 / 2)) hx₀central hx₁central
  have hdegree_nonneg : 0 ≤ (p.natDegree : ℝ) := Nat.cast_nonneg _
  have hmain : M / 2 ≤ 10 * (p.natDegree : ℝ) / M := by
    calc
      M / 2 ≤ |p.eval x₁ - p.eval x₀| := hseparation
      _ ≤ (2 * (p.natDegree : ℝ) * M) * |x₁ - x₀| := hmv
      _ ≤ (2 * (p.natDegree : ℝ) * M) * (5 / M ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 10 * (p.natDegree : ℝ) / M := by field_simp; ring
  have hclear := (le_div_iff₀ hMpos).mp hmain
  nlinarith

/-- Conditional form of the scoped degree lower bound, parameterized by the
product of the fixed constant and the accuracy. -/
theorem polynomial_natDegree_lower_of_derivative_bound
    (p : ℝ[X]) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 16)
    (hweighted : ∀ x ∈ Icc (-1 : ℝ) 1, |x| * (p.eval x) ^ 2 ≤ 1)
    (hzero : 1 / δ ≤ (p.eval 0) ^ 2)
    (hderiv : ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
        |p.derivative.eval x| ≤ 2 * (p.natDegree : ℝ) * M) :
    1 / (20 * δ) ≤ (p.natDegree : ℝ) := by
  have hzero_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, hzero_mem⟩ p.continuous.abs.continuousOn
  let M : ℝ := |p.eval x₀|
  have hMnonneg : 0 ≤ M := abs_nonneg _
  have hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M := by
    intro x hx
    exact hmax hx
  have hzeroM : (p.eval 0) ^ 2 ≤ M ^ 2 := by
    have hz := hbound 0 hzero_mem
    nlinarith [sq_abs (p.eval 0), abs_nonneg (p.eval 0)]
  have hcentral : 16 ≤ 1 / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hMsq : 16 ≤ M ^ 2 := hcentral.trans (hzero.trans hzeroM)
  have hdegree := polynomial_square_le_twenty_natDegree_of_central_derivative_bound
    p M x₀ rfl hMsq hx₀ hweighted (hderiv M hMnonneg hbound)
  have hscalar : 1 / δ ≤ 20 * (p.natDegree : ℝ) :=
    hzero.trans (hzeroM.trans hdegree)
  have hclear := (div_le_iff₀ hδ).mp hscalar
  apply (div_le_iff₀ (show 0 < 20 * δ by positivity)).mpr
  nlinarith

end
end HierarchicalAbsoluteSpectral
