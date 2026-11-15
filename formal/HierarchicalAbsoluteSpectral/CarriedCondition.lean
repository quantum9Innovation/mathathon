import HierarchicalAbsoluteSpectral.InverseMetric
import HierarchicalAbsoluteSpectral.Spectral

/-! Input-independent covariance bounds for the carried relative factor.
The bounds use only the hierarchy's floors and upper bounds in its D metric. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k n p : ℕ}

theorem matrix_norm_le_of_gram_le (M : Matrix (Fin n) (Fin p) ℝ) (a : ℝ) (ha : 0≤a)
    (hM : Mᵀ*M≤(a^2) • (1 : Core p)) : ‖M‖≤a := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro x
  change ‖toLp 2 (M*ᵥofLp x)‖≤a*‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
  have h := quadratic_mono hM (ofLp x)
  rw [quadratic_smul, quadratic_one_norm] at h
  have he : quadratic (Mᵀ*M) (ofLp x)=‖toLp 2 (M*ᵥofLp x)‖^2 := by
    rw [show Mᵀ*M=Mᵀ*(Mᵀ)ᵀ by simp, quadratic_mul_transpose]
    simpa only [Matrix.transpose_transpose] using quadratic_one_norm (toLp 2 (M*ᵥofLp x))
  rw [he] at h
  simpa only [mul_pow] using h

theorem metric_relative_bound (F G D : Core k) (B h : ℝ)
    (hB : 0≤B) (hh : 0<h) (hF : F≤B • D) (hG : (8*h) • D≤G) :
    F≤(B/(8*h)) • G := by
  apply hF.trans
  have hs := smul_le_smul_of_nonneg_left hG (by positivity : 0≤B/(8*h))
  convert hs using 1
  rw [smul_smul]
  congr 1
  field_simp

theorem carriedFactor_gram_bound (R₀ R D : Core k) (B₀ h : ℝ)
    (hR : IsUnit R.det) (hB : 0≤B₀) (hh : 0<h)
    (hF₀ : inverseMetric R₀ ≤ B₀ • D) (hF : (8*h) • D ≤ inverseMetric R) :
    (R₀⁻¹*R)ᵀ*(R₀⁻¹*R)≤(B₀/(8*h)) • (1 : Core k) := by
  have hc := star_left_conjugate_le_conjugate
    (metric_relative_bound _ _ D B₀ h hB hh hF₀ hF) R
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_smul, Matrix.smul_mul, inverseMetric_normalized R hR] at hc
  convert hc using 1
  simp only [inverseMetric, Matrix.transpose_mul, Matrix.mul_assoc]

theorem carried_factor_condition (R₀ R D : Core k) (B₀ B h₀ h : ℝ)
    (hR₀ : IsUnit R₀.det) (hR : IsUnit R.det)
    (hB₀ : 0≤B₀) (hB : 0≤B) (hh₀ : 0<h₀) (hh : 0<h)
    (hF₀lo : (8*h₀) • D ≤ inverseMetric R₀) (hF₀up : inverseMetric R₀ ≤ B₀ • D)
    (hFlo : (8*h) • D ≤ inverseMetric R) (hFup : inverseMetric R ≤ B • D) :
    let S := R₀⁻¹*R
    let Sinv := R⁻¹*R₀
    let a := (1+B/(8*h₀))⁻¹
    let b := 1+B₀/(8*h)
    let U := b*(1+B/(8*h₀))
    Sinv*S=1 ∧ 0<a ∧ ‖Sinv‖≤1/a ∧ ‖S‖≤b ∧ b/a≤U ∧ 1≤U := by
  dsimp only
  have hc₀ : 0≤B₀/(8*h) := by positivity
  have hc : 0≤B/(8*h₀) := by positivity
  have hn (M : Core k) (c : ℝ) (hc : 0≤c) (hG : Mᵀ*M≤c • (1 : Core k)) : ‖M‖≤1+c := by
    apply matrix_norm_le_of_gram_le M (1+c) (by positivity)
    exact hG.trans (smul_le_smul_of_nonneg_right
      (show c≤(1+c)^2 by nlinarith) (Matrix.PosSemidef.one : (1 : Core k).PosSemidef).nonneg)
  refine ⟨?_,by positivity,?_,?_,?_,?_⟩
  · calc
      _ = R⁻¹*(R₀*R₀⁻¹)*R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hR₀, Matrix.mul_one, Matrix.nonsing_inv_mul _ hR]
  · simpa only [one_div, inv_inv] using hn (R⁻¹*R₀) (B/(8*h₀)) hc
      (carriedFactor_gram_bound R R₀ D B h₀ hR₀ hB hh₀ hFup hF₀lo)
  · exact hn (R₀⁻¹*R) (B₀/(8*h)) hc₀
      (carriedFactor_gram_bound R₀ R D B₀ h hR hB₀ hh hF₀up hFlo)
  · simp only [div_eq_mul_inv, inv_inv]
    exact le_refl _
  · nlinarith

end
end HierarchicalAbsoluteSpectral
