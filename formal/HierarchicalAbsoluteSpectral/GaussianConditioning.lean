import HierarchicalAbsoluteSpectral.GaussianCapture

/-! Derive the covariance lower and upper bounds from the actual change
of coordinates S and its deterministic inverse-action bound. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem orthonormal_columns_mulVec_norm {k h : ℕ}
    (J : Matrix (Fin k) (Fin h) ℝ) (hJ : Jᵀ*J = 1) (u : Fin h → ℝ) :
    ‖(toLp 2 (J *ᵥ u) : EuclideanSpace ℝ (Fin k))‖ = ‖toLp 2 u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hq := quadratic_mul_transpose Jᵀ u
  rw [Matrix.transpose_transpose, hJ] at hq
  exact ((quadratic_one_norm (toLp 2 (J *ᵥ u))).symm.trans hq.symm).trans
    (quadratic_one_norm (toLp 2 u))

theorem gaussian_head_covariance_lower {k h : ℕ}
    (J : Matrix (Fin k) (Fin h) ℝ) (S Sinv : Core k)
    (hJ : Jᵀ*J = 1) (hSinv : Sinv*S = 1)
    (a : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (u : Fin h → ℝ) (hu : ∑ i, (u i)^2 = 1) :
    a^2 ≤ ∑ j, (∑ i, (Jᵀ*Sᵀ) i j*u i)^2 := by
  let v := J *ᵥ u
  let y := S *ᵥ v
  have hNu : ‖(toLp 2 u : EuclideanSpace ℝ (Fin h))‖ = 1 := by
    have hsq := EuclideanSpace.real_norm_sq_eq (toLp 2 u)
    nlinarith [norm_nonneg (toLp 2 u)]
  have hNv : ‖(toLp 2 v : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    dsimp only [v]
    rw [orthonormal_columns_mulVec_norm J hJ, hNu]
  have hback : Sinv *ᵥ y = v := by
    simp only [y, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  have hm := Matrix.l2_opNorm_mulVec Sinv (toLp 2 y)
  change ‖toLp 2 (Sinv *ᵥ y)‖ ≤ ‖Sinv‖*‖toLp 2 y‖ at hm
  rw [hback, hNv] at hm
  have hm' : 1 ≤ ‖(toLp 2 y : EuclideanSpace ℝ (Fin k))‖/a := by
    calc
      _ ≤ ‖Sinv‖*‖toLp 2 y‖ := hm
      _ ≤ (1/a)*‖toLp 2 y‖ := mul_le_mul_of_nonneg_right hInv (norm_nonneg _)
      _ = _ := by ring
  have hy : a ≤ ‖(toLp 2 y : EuclideanSpace ℝ (Fin k))‖ := by
    simpa using (le_div_iff₀ ha).mp hm'
  have hyvec : (fun j => ∑ i, (Jᵀ*Sᵀ) i j*u i) = y := by
    change (Jᵀ*Sᵀ)ᵀ *ᵥ u = y
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mulVec_mulVec]
  change a^2 ≤ ∑ j, ((fun j => ∑ i, (Jᵀ*Sᵀ) i j*u i) j)^2
  rw [hyvec, ← EuclideanSpace.real_norm_sq_eq (toLp 2 y)]
  nlinarith

theorem gaussian_rotated_start_norm {k t : ℕ}
    (Q : Matrix (Fin k) (Fin t) ℝ) (S : Core k) (hQ : Qᵀ*Q = 1) :
    ‖Qᵀ*Sᵀ‖ ≤ ‖S‖ := by
  calc
    _ ≤ ‖Qᵀ‖*‖Sᵀ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1*‖S‖ := by
      rw [spectral_norm_transpose, spectral_norm_transpose]
      exact mul_le_mul_of_nonneg_right (orthonormal_columns_norm_le_one Q hQ) (norm_nonneg _)
    _ = _ := one_mul _

end
end HierarchicalAbsoluteSpectral
