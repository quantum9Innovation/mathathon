import HierarchicalAbsoluteSpectral.AnalyticInverseRoot
import Mathlib.MeasureTheory.Integral.CircleAverage

/-! Cauchy bounds for Fourier coefficients, with the contour and its
deformation both proved in the underlying complex analysis library. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Complex Set Metric MeasureTheory
open scoped Real ComplexConjugate

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def contourCoefficient (F : ℂ → ℂ) (n : ℕ) (R : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ • ∮ w in C(0,R), w⁻¹ • ((w^n)⁻¹ • F w)

theorem contourCoefficient_eq (F : ℂ → ℂ) (n : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hF : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ ≤ R → DifferentiableAt ℂ F w) :
    contourCoefficient F n R = contourCoefficient F n 1 := by
  have hdiff : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ ≤ R →
      DifferentiableAt ℂ (fun w => (w^n)⁻¹ • F w) w := by
    intro w hw hw'
    have hne : w ≠ 0 := by intro heq; norm_num [heq] at hw
    exact ((differentiableAt_id.pow n).inv (pow_ne_zero n hne)).smul (hF w hw hw')
  have hc : ContinuousOn (fun w => (w^n)⁻¹ • F w) (closedBall 0 R \ ball 0 1) := by
    intro w hw
    have h1 : 1 ≤ ‖w‖ := by simpa using hw.2
    have h2 : ‖w‖ ≤ R := by simpa using hw.1
    exact (hdiff w h1 h2).continuousAt.continuousWithinAt
  have hd : ∀ w ∈ (ball 0 R \ closedBall 0 1) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w => (w^n)⁻¹ • F w) w := by
    intro w hw
    have h1 : 1 ≤ ‖w‖ := by have : 1 < ‖w‖ := by simpa using hw.1.2; exact this.le
    have h2 : ‖w‖ ≤ R := by have : ‖w‖ < R := by simpa using hw.1.1; exact this.le
    exact hdiff w h1 h2
  unfold contourCoefficient
  congr 1
  simpa using Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    (by norm_num : (0 : ℝ) < 1) hR Set.countable_empty hc hd

theorem contourCoefficient_norm_le (F : ℂ → ℂ) (n : ℕ) (R M : ℝ) (hR : 0 < R)
    (hF : ∀ w : ℂ, ‖w‖ = R → ‖F w‖ ≤ M) :
    ‖contourCoefficient F n R‖ ≤ M*(R⁻¹)^n := by
  have hb : ∀ w ∈ sphere (0 : ℂ) R,
      ‖w⁻¹ • ((w^n)⁻¹ • F w)‖ ≤ R⁻¹*((R⁻¹)^n*M) := by
    intro w hw
    have hn : ‖w‖ = R := by simpa using hw
    simp only [norm_smul, norm_inv, norm_pow, hn, ← inv_pow]
    gcongr
    exact hF w hn
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hb
  change ‖contourCoefficient F n R‖ ≤ R*(R⁻¹*((R⁻¹)^n*M)) at h
  convert h using 1
  field_simp

theorem fourier_nat_power (n : ℕ) (t : AddCircle (2*Real.pi)) :
    AddCircle.fourier (n : ℤ) t = (AddCircle.fourier 1 t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, AddCircle.fourier_add, ih, pow_succ]

theorem fourier_neg_nat_power (n : ℕ) (t : AddCircle (2*Real.pi)) :
    AddCircle.fourier (-(n : ℤ)) t = ((AddCircle.fourier 1 t)^n)⁻¹ := by
  rw [AddCircle.fourier_neg, fourier_nat_power]
  apply (Complex.inv_eq_conj ?_).symm
  simp only [norm_pow, AddCircle.fourier_apply, Circle.norm_coe, one_pow]

theorem unit_circle_fourier (θ : ℝ) :
    circleMap 0 1 θ = AddCircle.fourier 1 (θ : AddCircle (2*Real.pi)) := by
  rw [AddCircle.fourier_coe_apply]
  simp only [circleMap, ofReal_one, one_mul, zero_add, Int.cast_one, mul_one,
    ofReal_mul, ofReal_ofNat]
  congr 1
  field_simp
  ring

theorem fourierCoeff_eq_contour (f : C(AddCircle (2*Real.pi), ℂ))
    (F : ℂ → ℂ) (n : ℕ)
    (hF : ∀ t : AddCircle (2*Real.pi), f t = F (AddCircle.fourier 1 t)) :
    AddCircle.fourierCoeff f (n : ℤ) = contourCoefficient F n 1 := by
  rw [AddCircle.fourierCoeff_eq_intervalIntegral _ _ 0]
  have heq : (fun θ : ℝ => AddCircle.fourier (-(n : ℤ)) (θ : AddCircle (2*Real.pi)) •
      f (θ : AddCircle (2*Real.pi))) =
      (fun θ : ℝ => ((circleMap 0 1 θ)^n)⁻¹ • F (circleMap 0 1 θ)) := by
    funext θ
    rw [hF, fourier_neg_nat_power, unit_circle_fourier]
  rw [zero_add, heq]
  change circleAverage (fun w : ℂ => (w^n)⁻¹ • F w) 0 1 = _
  simpa [contourCoefficient] using
    circleAverage_eq_circleIntegral (f := fun w : ℂ => (w^n)⁻¹ • F w)
      (c := 0) (R := 1) (by norm_num : (1 : ℝ) ≠ 0)

theorem fourierCoeff_cauchy_bound (f : C(AddCircle (2*Real.pi), ℂ))
    (F : ℂ → ℂ) (R M : ℝ) (hR : 1 ≤ R)
    (hF : ∀ t : AddCircle (2*Real.pi), f t = F (AddCircle.fourier 1 t))
    (hd : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ ≤ R → DifferentiableAt ℂ F w)
    (hb : ∀ w : ℂ, ‖w‖ = R → ‖F w‖ ≤ M) (n : ℕ) :
    ‖AddCircle.fourierCoeff f (n : ℤ)‖ ≤ M*(R⁻¹)^n := by
  rw [fourierCoeff_eq_contour f F n hF, ← contourCoefficient_eq F n R hR hd]
  exact contourCoefficient_norm_le F n R M (by linarith) hb

end
end HierarchicalAbsoluteSpectral
