import HierarchicalAbsoluteSpectral.IdealMetric
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
The finite polynomial congruence of Lemma 5. Starting with the explicit
scalar approximation property of a polynomial, derive invertibility and
the two relative Loewner bounds for the actual factor R*p(A).
The construction of the uniform polynomial with its degree/cost bound is
the separate approximation theorem; no metric closeness is assumed here.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Polynomial
open scoped MatrixOrder
variable {k : ℕ}

theorem scalar_inverse_square_relative (f p τ : ℝ)
    (hf : 0 < f) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/4)
    (happrox : |p * Real.sqrt f - 1| ≤ τ) :
    0 < p ∧ (1-4*τ)*f ≤ (p⁻¹)^2 ∧ (p⁻¹)^2 ≤ (1+4*τ)*f := by
  have hs : 0 < Real.sqrt f := Real.sqrt_pos.mpr hf
  have hroot := Real.sq_sqrt hf.le
  have hband := abs_le.mp happrox
  have hz : 0 < p * Real.sqrt f := by linarith
  have hp : 0 < p := (mul_pos_iff.mp hz).resolve_right (by intro h; linarith [h.2]) |>.1
  have hzlo : 1-τ ≤ p * Real.sqrt f := by linarith
  have hzup : p * Real.sqrt f ≤ 1+τ := by linarith
  have hzlo2 := (sq_le_sq₀ (by linarith : 0 ≤ 1-τ) hz.le).mpr hzlo
  have hzup2 := (sq_le_sq₀ hz.le (by positivity : 0 ≤ 1+τ)).mpr hzup
  have hlo := mul_le_mul_of_nonneg_left hzup2 (show 0 ≤ 1-4*τ by linarith)
  have hup := mul_le_mul_of_nonneg_left hzlo2 (show 0 ≤ 1+4*τ by positivity)
  have hcube : 0 ≤ τ^3 := by positivity
  have ht2 := mul_le_mul_of_nonneg_left hτ' hτ
  have hlobudget : (1-4*τ)*(1+τ)^2 ≤ 1 := by nlinarith [sq_nonneg τ]
  have hupbudget : 1 ≤ (1+4*τ)*(1-τ)^2 := by nlinarith
  have hzsq : p^2*f = (p*Real.sqrt f)^2 := by rw [mul_pow, hroot]
  have hinv : p^2*(p⁻¹)^2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne']; norm_num
  have hp2 : 0 < p^2 := sq_pos_of_pos hp
  refine ⟨hp, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ hp2).mp
    rw [hinv]
    calc
      _ = (1-4*τ)*(p^2*f) := by ring
      _ = (1-4*τ)*(p*Real.sqrt f)^2 := by rw [hzsq]
      _ ≤ 1 := hlo.trans hlobudget
  · apply (mul_le_mul_iff_right₀ hp2).mp
    rw [hinv]
    calc
      1 ≤ (1+4*τ)*(p*Real.sqrt f)^2 := hupbudget.trans hup
      _ = (1+4*τ)*(p^2*f) := by rw [hzsq]
      _ = p^2*((1+4*τ)*f) := by ring

theorem polynomial_inverseMetric_relative (A : Core k) (hA : A.IsHermitian)
    (η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/4)
    (p : ℝ[X])
    (happrox : ∀ x ∈ spectrum ℝ A,
      |p.eval x * Real.sqrt (absoluteRootScalar η x) - 1| ≤ τ) :
    (aeval A p).PosDef ∧
    (1-4*τ) • absoluteRootMatrix A η ≤ inverseMetric (aeval A p) ∧
    inverseMetric (aeval A p) ≤ (1+4*τ) • absoluteRootMatrix A η := by
  have hb (x : ℝ) (hx : x ∈ spectrum ℝ A) :=
    scalar_inverse_square_relative (absoluteRootScalar η x) (p.eval x) τ
      (scalar_absolute_root_pos η x hη) hτ hτ' (happrox x hx)
  have hpoly : cfc (p := IsSelfAdjoint) p.eval A = aeval A p :=
    cfc_polynomial p A hA
  have hpos : (aeval A p).PosDef := by
    apply Matrix.IsStrictlyPositive.posDef
    rw [← hpoly]
    exact (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) p.eval A
      (finite_spectrum_continuous A _) hA).mpr (fun x hx => (hb x hx).1)
  have hinv : cfc (p := IsSelfAdjoint) (fun x => (p.eval x)⁻¹) A = (aeval A p)⁻¹ := by
    simpa [hpoly, Matrix.nonsing_inv_eq_ringInverse] using
      cfc_inv (p := IsSelfAdjoint) p.eval A (fun x hx => (hb x hx).1.ne')
        (finite_spectrum_continuous A _) hA
  have hmetric : cfc (p := IsSelfAdjoint) (fun x => ((p.eval x)⁻¹)^2) A =
      inverseMetric (aeval A p) := by
    rw [cfc_pow (p := IsSelfAdjoint) _ 2 A (finite_spectrum_continuous A _), hinv]
    have hsym : ((aeval A p)⁻¹)ᵀ = (aeval A p)⁻¹ := by
      exact hpos.inv.isHermitian.eq
    simp [inverseMetric, hsym, pow_two]
  have hlo := cfc_mono (p := IsSelfAdjoint) (a := A)
    (fun x hx => (hb x hx).2.1) (finite_spectrum_continuous A _) (finite_spectrum_continuous A _)
  have hup := cfc_mono (p := IsSelfAdjoint) (a := A)
    (fun x hx => (hb x hx).2.2) (finite_spectrum_continuous A _) (finite_spectrum_continuous A _)
  rw [hmetric, cfc_const_mul (p := IsSelfAdjoint) _ _ A (finite_spectrum_continuous A _)] at hlo hup
  exact ⟨hpos, hlo, hup⟩

def refinedInverseFactor (R Kj : Core k) (ε : ℝ) (p : ℝ[X]) : Core k :=
  let Rp := inflatedInverseFactor R ε
  Rp * aeval (Rpᵀ * Kj * Rp) p

theorem refinedInverseFactor_relative (R Kj : Core k) (hR : IsUnit R.det)
    (hKj : Kjᵀ = Kj) (ε τ : ℝ) (hε : 0 < ε)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/4) (p : ℝ[X])
    (happrox : ∀ x ∈ spectrum ℝ
        ((inflatedInverseFactor R ε)ᵀ * Kj * inflatedInverseFactor R ε),
      |p.eval x * Real.sqrt (absoluteRootScalar (8*ε) x) - 1| ≤ τ) :
    IsUnit (refinedInverseFactor R Kj ε p).det ∧
    (1-4*τ) • idealMetric (inflatedInverseFactor R ε) Kj (8*ε) ≤
      inverseMetric (refinedInverseFactor R Kj ε p) ∧
    inverseMetric (refinedInverseFactor R Kj ε p) ≤
      (1+4*τ) • idealMetric (inflatedInverseFactor R ε) Kj (8*ε) := by
  let Rp := inflatedInverseFactor R ε
  have hRp : IsUnit Rp.det := inflatedInverseFactor_isUnit R hR ε hε.le
  have hrelative := polynomial_inverseMetric_relative (Rpᵀ*Kj*Rp)
    (normalized_isHermitian Rp Kj hKj) (8*ε) τ (by positivity) hτ hτ' p happrox
  have hunit : IsUnit (refinedInverseFactor R Kj ε p).det := by
    change IsUnit (Rp * aeval (Rpᵀ*Kj*Rp) p).det
    rw [Matrix.det_mul]
    exact hRp.mul ((Matrix.isUnit_iff_isUnit_det _).mp hrelative.1.isUnit)
  have hlo := star_left_conjugate_le_conjugate hrelative.2.1 Rp⁻¹
  have hup := star_left_conjugate_le_conjugate hrelative.2.2 Rp⁻¹
  constructor
  · exact hunit
  · constructor
    · simpa [refinedInverseFactor, inverseMetric_mul, idealMetric, Rp,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.mul_smul, Matrix.smul_mul] using hlo
    · simpa [refinedInverseFactor, inverseMetric_mul, idealMetric, Rp,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.mul_smul, Matrix.smul_mul] using hup

end
end HierarchicalAbsoluteSpectral
