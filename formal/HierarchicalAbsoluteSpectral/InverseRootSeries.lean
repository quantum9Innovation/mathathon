import HierarchicalAbsoluteSpectral.CircleCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! The Chebyshev series of the inverse-root function. Its coefficients
are used to prove an error bound, not as an oracle for the finite algorithm. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Complex Polynomial Polynomial.Chebyshev Set
open scoped Real ComplexConjugate

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

theorem complexInverseRoot_real_continuous (η : ℝ) (hη : 0 < η) :
    Continuous (fun x : ℝ => complexInverseRoot η (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hg := (complexInverseRoot_differentiableAt η (x : ℂ) hη
    (by simp only [ofReal_im, abs_zero]; positivity)).continuousAt
  exact hg.comp continuous_ofReal.continuousAt

def inverseRootCircle (η : ℝ) (hη : 0 < η) : C(AddCircle (2*Real.pi), ℂ) where
  toFun t := complexInverseRoot η ((fourier 1 t).re : ℂ)
  continuous_toFun := (complexInverseRoot_real_continuous η hη).comp
    (continuous_re.comp (fourier 1).continuous)

theorem joukowski_unit (w : ℂ) (hw : ‖w‖ = 1) :
    joukowski w = (w.re : ℂ) := by
  rw [joukowski, Complex.inv_eq_conj hw]
  apply Complex.ext <;> simp

theorem inverseRootCircle_joukowski (η : ℝ) (hη : 0 < η)
    (t : AddCircle (2*Real.pi)) :
    inverseRootCircle η hη t = complexInverseRoot η (joukowski (fourier 1 t)) := by
  rw [joukowski_unit _ (by simp only [fourier_apply, Circle.norm_coe])]
  rfl

theorem inverseRootCircle_real (η : ℝ) (hη : 0 < η)
    (t : AddCircle (2*Real.pi)) :
    conj (inverseRootCircle η hη t) = inverseRootCircle η hη t := by
  change conj (complexInverseRoot η _) = complexInverseRoot η _
  rw [complexInverseRoot_ofReal η _ hη]
  simp

theorem inverseRootCircle_even (η : ℝ) (hη : 0 < η)
    (t : AddCircle (2*Real.pi)) :
    inverseRootCircle η hη (-t) = inverseRootCircle η hη t := by
  change complexInverseRoot η ((fourier 1 (-t)).re : ℂ) = _
  rw [fourier_neg_argument, fourier_neg]
  simp only [conj_re]
  rfl

theorem inverseRootCircle_at_angle (η θ : ℝ) (hη : 0 < η) :
    inverseRootCircle η hη (θ : AddCircle (2*Real.pi)) =
      (inverseRootValue η (Real.cos θ) : ℂ) := by
  change complexInverseRoot η ((fourier 1 (θ : AddCircle (2*Real.pi))).re : ℂ) = _
  rw [← unit_circle_fourier]
  simp only [circleMap, ofReal_one, one_mul, zero_add, exp_ofReal_mul_I_re]
  exact complexInverseRoot_ofReal η _ hη

theorem inverseRoot_fourier_bound (η : ℝ) (hη : 0 < η) (n : ℕ) :
    ‖fourierCoeff (inverseRootCircle η hη) (n : ℤ)‖ ≤
      (Real.sqrt η)⁻¹*((1+η/4)⁻¹)^n := by
  apply fourierCoeff_cauchy_bound (inverseRootCircle η hη)
    (fun w => complexInverseRoot η (joukowski w)) (1+η/4) (Real.sqrt η)⁻¹
    (by linarith)
  · exact inverseRootCircle_joukowski η hη
  · exact fun w hw hw' => inverseRoot_joukowski_differentiableAt η w hη hw hw'
  · exact fun w _ => complexInverseRoot_norm_le η (joukowski w) hη

theorem inverseRoot_fourier_summable (η : ℝ) (hη : 0 < η) :
    Summable (fourierCoeff (inverseRootCircle η hη)) := by
  have hr0 : 0 ≤ (1+η/4)⁻¹ := by positivity
  have hr1 : (1+η/4)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr (by linarith)
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.sqrt η)⁻¹
  have hp : Summable (fun n : ℕ => fourierCoeff (inverseRootCircle η hη) (n : ℤ)) :=
    hgeom.of_norm_bounded (inverseRoot_fourier_bound η hη)
  have hn : Summable (fun n : ℕ => fourierCoeff (inverseRootCircle η hη) (-(n : ℤ))) := by
    exact hp.congr fun n => (fourierCoeff_neg_of_even _ (inverseRootCircle_even η hη) _).symm
  exact Summable.of_nat_of_neg hp hn

def inverseRootChebyshevCoeff (η : ℝ) (hη : 0 < η) (n : ℕ) : ℝ :=
  if n = 0 then (fourierCoeff (inverseRootCircle η hη) 0).re
  else 2*(fourierCoeff (inverseRootCircle η hη) (n : ℤ)).re

theorem inverseRootChebyshevCoeff_bound (η : ℝ) (hη : 0 < η) (n : ℕ) :
    |inverseRootChebyshevCoeff η hη n| ≤
      2*(Real.sqrt η)⁻¹*((1+η/4)⁻¹)^n := by
  have h := inverseRoot_fourier_bound η hη n
  have hr := Complex.abs_re_le_norm (fourierCoeff (inverseRootCircle η hη) (n : ℤ))
  by_cases hn : n = 0
  · subst n
    simp only [inverseRootChebyshevCoeff, ↓reduceIte, pow_zero, mul_one, Nat.cast_zero] at *
    have hs : 0 ≤ (Real.sqrt η)⁻¹ := by positivity
    linarith
  · simp only [inverseRootChebyshevCoeff, hn, ↓reduceIte, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith

theorem inverseRootChebyshev_hasSum_cos (η θ : ℝ) (hη : 0 < η) :
    HasSum (fun n : ℕ => inverseRootChebyshevCoeff η hη n * (T ℝ (n : ℤ)).eval (Real.cos θ))
      (inverseRootValue η (Real.cos θ)) := by
  let f := inverseRootCircle η hη
  let c := fourierCoeff f
  have hc (n : ℤ) : (c n).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    rw [← fourierCoeff_neg_of_real f (inverseRootCircle_real η hη),
      fourierCoeff_neg_of_even f (inverseRootCircle_even η hη)]
  have hs := has_pointwise_sum_fourier_series_of_summable
    (inverseRoot_fourier_summable η hη) (θ : AddCircle (2*Real.pi))
  have hp := hs.nat_add_neg
  have hp' := hp.sub (hasSum_ite_eq (0 : ℕ) (c 0))
  have hsum := Complex.hasSum_re hp'
  convert hsum using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [inverseRootChebyshevCoeff, c, f]
    · have heq : c (-(n : ℤ)) = c (n : ℤ) :=
        fourierCoeff_neg_of_even f (inverseRootCircle_even η hη) _
      have harg : (fourier (n : ℤ) (θ : AddCircle (2*Real.pi))).re =
          Real.cos ((n : ℝ)*θ) := by
        rw [fourier_coe_apply]
        simp only [Int.cast_natCast, ofReal_mul, ofReal_ofNat]
        have hh : 2*Real.pi*I*(n : ℂ)*(θ : ℂ)/(2*Real.pi) = ((n : ℝ)*θ : ℝ)*I := by
          push_cast
          field_simp
        rw [hh, exp_ofReal_mul_I_re]
      change inverseRootChebyshevCoeff η hη n * (T ℝ (n : ℤ)).eval (Real.cos θ) =
        (c (n : ℤ) * fourier (n : ℤ) (θ : AddCircle (2*Real.pi)) +
          c (-(n : ℤ)) * fourier (-(n : ℤ)) (θ : AddCircle (2*Real.pi)) -
          if n = 0 then c 0 else 0).re
      rw [if_neg hn, sub_zero, heq, fourier_neg]
      simp only [Complex.add_re, Complex.mul_re, hc, zero_mul, sub_zero, conj_re, harg]
      simp only [inverseRootChebyshevCoeff, hn, ↓reduceIte, T_real_cos]
      change 2*(c (n : ℤ)).re*Real.cos ((n : ℝ)*θ) = _
      ring
  · simp [f, c, inverseRootCircle_at_angle]

theorem inverseRootChebyshev_hasSum (η x : ℝ) (hη : 0 < η) (hx : x ∈ Icc (-1:ℝ) 1) :
    HasSum (fun n : ℕ => inverseRootChebyshevCoeff η hη n * (T ℝ (n : ℤ)).eval x)
      (inverseRootValue η x) := by
  simpa only [Real.cos_arccos hx.1 hx.2] using
    inverseRootChebyshev_hasSum_cos η (Real.arccos x) hη

end
end HierarchicalAbsoluteSpectral
