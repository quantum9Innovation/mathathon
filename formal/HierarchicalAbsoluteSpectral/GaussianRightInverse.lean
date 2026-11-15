import HierarchicalAbsoluteSpectral.GaussianLinear
import HierarchicalAbsoluteSpectral.StrongFilterResidual
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
The complement of the quantified Gaussian small-ball event gives an actual
matrix inverse with an explicit spectral-norm bound. No inverse certificate
is supplied as a hypothesis.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

def columnsMatrix {m n : ℕ} (G : Fin n → Fin m → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => G j i

theorem columnCombination_eq_mulVec {m n : ℕ} (G : Fin n → Fin m → ℝ) (x : Fin n → ℝ) :
    columnCombination G x = columnsMatrix G *ᵥ x := by
  ext j
  simp only [columnCombination, columnsMatrix, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem columnOutputEnergy_smul {m n : ℕ} (G : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ) (c : ℝ) :
    columnOutputEnergy G (c • x) = c^2*columnOutputEnergy G x := by
  unfold columnOutputEnergy columnCombination
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_pow]

theorem energy_lower_of_not_gaussianSquareBad {n : ℕ}
    (G : Fin n → Fin n → ℝ) (s : ℝ) (hG : G ∉ gaussianSquareBad n s)
    (x : Fin n → ℝ) : s^2*‖x‖^2 ≤ columnOutputEnergy G x := by
  by_cases hx : x = 0
  · subst x
    simp [columnOutputEnergy, columnCombination]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  have hne : ¬columnOutputEnergy G (‖x‖⁻¹ • x) ≤ s^2 := by
    intro he
    exact hG ((gaussianSquareBad_iff n s G).mpr ⟨_,hu,he⟩)
  have hlt : s^2 < ‖x‖⁻¹^2*columnOutputEnergy G x := by
    simpa only [columnOutputEnergy_smul] using lt_of_not_ge hne
  have heq : (‖x‖⁻¹^2*columnOutputEnergy G x)*‖x‖^2 = columnOutputEnergy G x := by
    field_simp
  have hm := mul_le_mul_of_nonneg_right hlt.le (sq_nonneg ‖x‖)
  rwa [heq] at hm

theorem gaussianSquare_det_ne_zero {n : ℕ}
    (G : Fin n → Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    (hG : G ∉ gaussianSquareBad n s) : (columnsMatrix G).det ≠ 0 := by
  intro hd
  obtain ⟨x,hx,hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have he := energy_lower_of_not_gaussianSquareBad G s hG x
  have hE0 : columnOutputEnergy G x = 0 := by
    unfold columnOutputEnergy
    rw [columnCombination_eq_mulVec, hAx]
    simp
  rw [hE0] at he
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  nlinarith [mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos hnorm)]

theorem euclidean_norm_sq_le_card_pi_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2 ≤ n*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, ‖x‖^2 := Finset.sum_le_sum fun i _ => by
      have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
      nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]
    _ = _ := by simp

theorem gaussianSquare_inverse_norm {n : ℕ}
    (G : Fin n → Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    (hG : G ∉ gaussianSquareBad n s) :
    ‖(columnsMatrix G)⁻¹‖ ≤ Real.sqrt n/s := by
  have hd := gaussianSquare_det_ne_zero G s hs hG
  have hinv : columnsMatrix G*(columnsMatrix G)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖toLp 2 ((columnsMatrix G)⁻¹ *ᵥ ofLp y)‖ ≤ (Real.sqrt n/s)*‖y‖
  let x := (columnsMatrix G)⁻¹ *ᵥ ofLp y
  have hAx : columnsMatrix G *ᵥ x = ofLp y := by
    simp only [x, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have he := energy_lower_of_not_gaussianSquareBad G s hG x
  have hE : columnOutputEnergy G x = ‖y‖^2 := by
    unfold columnOutputEnergy
    rw [columnCombination_eq_mulVec, hAx, EuclideanSpace.real_norm_sq_eq]
  rw [hE] at he
  have hx := euclidean_norm_sq_le_card_pi_norm_sq x
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hmain : ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2*s^2 ≤ n*‖y‖^2 := by
    have h1 := mul_le_mul_of_nonneg_right hx (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left he hn
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2 ≤ ((Real.sqrt n/s)*‖y‖)^2
  rw [mul_pow, div_pow, Real.sq_sqrt hn]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hs)).mpr hmain

end
end HierarchicalAbsoluteSpectral
