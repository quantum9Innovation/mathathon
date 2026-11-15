import HierarchicalAbsoluteSpectral.GaussianRightInverse
import HierarchicalAbsoluteSpectral.GaussianEnergy
import HierarchicalAbsoluteSpectral.GaussianRestriction

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

def columnEmbedding {h r : ℕ} (e : Fin h ↪ Fin r) : Matrix (Fin r) (Fin h) ℝ :=
  (1 : Core r).submatrix id e

theorem columnEmbedding_gram {h r : ℕ} (e : Fin h ↪ Fin r) :
    (columnEmbedding e)ᵀ*columnEmbedding e = 1 := by
  rw [columnEmbedding, Matrix.transpose_submatrix, Matrix.transpose_one]
  calc
    _ = ((1 : Core r).submatrix id e).submatrix e id := by
      simpa using Matrix.one_submatrix_mul e (Equiv.refl (Fin r))
        ((1 : Core r).submatrix id e)
    _ = 1 := by
      simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
        Matrix.submatrix_one (α := ℝ) e e.injective

theorem matrix_identity_norm_le_one (n : ℕ) : ‖(1 : Core n)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖toLp 2 ((1 : Core n) *ᵥ ofLp x)‖ ≤ 1*‖x‖
  simp

theorem orthonormal_columns_norm_le_one {h r : ℕ}
    (J : Matrix (Fin r) (Fin h) ℝ) (hJ : Jᵀ*J = 1) : ‖J‖ ≤ 1 := by
  have heq : ‖J‖*‖J‖ = ‖(1 : Core h)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
      Matrix.conjTranspose_eq_transpose_of_trivial, hJ]
  nlinarith [matrix_identity_norm_le_one h, norm_nonneg J]

theorem columnEmbedding_norm_le_one {h r : ℕ} (e : Fin h ↪ Fin r) : ‖columnEmbedding e‖ ≤ 1 :=
  orthonormal_columns_norm_le_one _ (columnEmbedding_gram e)

theorem columnsMatrix_mul_columnEmbedding {m h r : ℕ}
    (G : Fin r → Fin m → ℝ) (e : Fin h ↪ Fin r) :
    columnsMatrix G*columnEmbedding e = columnsMatrix (fun j => G (e j)) := by
  calc
    _ = (columnsMatrix G).submatrix id e := by
      simpa only [columnEmbedding, Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
        Matrix.mul_submatrix_one (Equiv.refl (Fin r)) e (columnsMatrix G)
    _ = _ := rfl

/-- The spectral norm is bounded by the actual finite sum of squared entries. -/
theorem columnsMatrix_norm_le_energy {m r : ℕ}
    (G : Fin r → Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t) (hE : gaussianEnergy G ≤ t^2) :
    ‖columnsMatrix G‖ ≤ t := by
  apply spectral_norm_le_of_rayleigh _ t ht
  intro x
  rw [quadratic_mul_transpose]
  have hq : quadratic (1 : Core r) ((columnsMatrix G)ᵀ *ᵥ x) =
      ∑ j, (∑ i, G j i*x i)^2 := by
    rw [quadratic, Matrix.one_mulVec]
    simp [dotProduct, Matrix.mulVec, columnsMatrix, pow_two]
  rw [hq]
  have hc : (∑ j, (∑ i, G j i*x i)^2) ≤
      gaussianEnergy G*(∑ i, (x i)^2) := by
    calc
      _ ≤ ∑ j, (∑ i, (G j i)^2)*(∑ i, (x i)^2) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hqx : quadratic (1 : Core m) x = ∑ i, (x i)^2 := by
    rw [quadratic, Matrix.one_mulVec]
    simp [dotProduct, pow_two]
  rw [hqx]
  exact hc.trans (mul_le_mul_of_nonneg_right hE (by positivity))

def gaussianHeadRightInverse {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r)
    (G : Fin r → Fin k → ℝ) : Matrix (Fin r) (Fin h) ℝ :=
  columnEmbedding e * (columnsMatrix (gaussianLinearColumns A (fun j => G (e j))))⁻¹

theorem gaussianHeadRightInverse_identity {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r)
    (G : Fin r → Fin k → ℝ) (s : ℝ) (hs : 0 < s)
    (hG : gaussianLinearColumns A (fun j => G (e j)) ∉ gaussianSquareBad h s) :
    columnsMatrix (gaussianLinearColumns A G)*gaussianHeadRightInverse A e G = 1 := by
  rw [gaussianHeadRightInverse, ← Matrix.mul_assoc, columnsMatrix_mul_columnEmbedding]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (gaussianSquare_det_ne_zero _ s hs hG))

theorem gaussianHeadRightInverse_norm {h k r : ℕ}
    (A : Matrix (Fin h) (Fin k) ℝ) (e : Fin h ↪ Fin r)
    (G : Fin r → Fin k → ℝ) (s : ℝ) (hs : 0 < s)
    (hG : gaussianLinearColumns A (fun j => G (e j)) ∉ gaussianSquareBad h s) :
    ‖gaussianHeadRightInverse A e G‖ ≤ Real.sqrt h/s := by
  calc
    _ ≤ ‖columnEmbedding e‖*‖(columnsMatrix (gaussianLinearColumns A (fun j => G (e j))))⁻¹‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ 1*(Real.sqrt h/s) := by
      exact mul_le_mul (columnEmbedding_norm_le_one e)
        (gaussianSquare_inverse_norm _ s hs hG) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end
end HierarchicalAbsoluteSpectral
