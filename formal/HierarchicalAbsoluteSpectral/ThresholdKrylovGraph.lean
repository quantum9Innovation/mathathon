import HierarchicalAbsoluteSpectral.ThresholdKrylovRayleigh
import HierarchicalAbsoluteSpectral.ThresholdKrylovScalar

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp Polynomial
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k h r : ℕ}

def spectralMask (bad : Fin k → Prop) [DecidablePred bad] : Core k :=
  Matrix.diagonal (fun i => if bad i then 1 else 0)

theorem diagonalFilteredGraph_mask (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ)
    (bad : Fin k → Prop) [DecidablePred bad] :
    spectralMask bad*diagonalFilteredGraph d p e Ω H =
      Matrix.diagonal (fun i => if bad i then p.eval (d i) else 0)*(Ω*H)*
        Matrix.diagonal (fun s => (p.eval (d (e s)))⁻¹) := by
  have hd : spectralMask bad*Matrix.diagonal (fun i => p.eval (d i)) =
      Matrix.diagonal (fun i => if bad i then p.eval (d i) else 0) := by
    rw [spectralMask, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hb : bad i <;> simp [hb]
  simp only [diagonalFilteredGraph, ← Matrix.mul_assoc]
  rw [hd]

theorem diagonalFilteredGraph_mask_norm (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ)
    (bad : Fin k → Prop) [DecidablePred bad] (a R : ℝ) (ha : 0 ≤ a)
    (hhead : ∀ s, 1 ≤ p.eval (d (e s))) (htail : ∀ i, bad i → |p.eval (d i)| ≤ a)
    (hΩ : ‖Ω*H‖ ≤ R) :
    ‖spectralMask bad*diagonalFilteredGraph d p e Ω H‖ ≤ a*R := by
  have hdiag : ‖Matrix.diagonal (fun i => if bad i then p.eval (d i) else 0)‖ ≤ a := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg ha).mpr
    intro i
    by_cases hb : bad i
    · simpa only [hb, if_true, Real.norm_eq_abs] using htail i hb
    · simp [hb, ha]
  have hinv : ‖Matrix.diagonal (fun s => (p.eval (d (e s)))⁻¹)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro s
    have hp : 0 ≤ (p.eval (d (e s)))⁻¹ := inv_nonneg.mpr (by linarith [hhead s])
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using inv_le_one_of_one_le₀ (hhead s)
  have hR : 0 ≤ R := (norm_nonneg _).trans hΩ
  rw [diagonalFilteredGraph_mask]
  calc
    _ ≤ (‖Matrix.diagonal (fun i => if bad i then p.eval (d i) else 0)‖*‖Ω*H‖)*
        ‖Matrix.diagonal (fun s => (p.eval (d (e s)))⁻¹)‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (a*R)*1 := by gcongr
    _ = a*R := mul_one _

theorem matrix_toEuclideanLin_norm_le {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (z : EuclideanSpace ℝ (Fin b)) :
    ‖M.toEuclideanLin z‖ ≤ ‖M‖*‖z‖ := by
  exact ContinuousLinearMap.le_opNorm M.toEuclideanLin.toContinuousLinearMap z

theorem masked_energy_eq_norm (bad : Fin k → Prop) [DecidablePred bad]
    (y : EuclideanSpace ℝ (Fin k)) :
    (∑ i, if bad i then (y i)^2 else 0) = ‖(spectralMask bad).toEuclideanLin y‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [spectralMask, Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hb : bad i <;> simp [hb]

theorem filteredGraph_low_energy (d : Fin k → ℝ) (p : ℝ[X]) (e : Fin h ↪ Fin k)
    (Ω : Matrix (Fin k) (Fin r) ℝ) (H : Matrix (Fin r) (Fin h) ℝ)
    (bad : Fin k → Prop) [DecidablePred bad] (a R ε : ℝ) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hhead : ∀ s, 1 ≤ p.eval (d (e s))) (htail : ∀ i, bad i → |p.eval (d i)| ≤ a)
    (hΩ : ‖Ω*H‖ ≤ R) (hsmall : a*R ≤ ε/10)
    (z : EuclideanSpace ℝ (Fin h)) :
    let y := (diagonalFilteredGraph d p e Ω H).toEuclideanLin z
    (∑ i, if bad i then (y i)^2 else 0) ≤ ε*∑ s, (z s)^2 := by
  dsimp only
  rw [masked_energy_eq_norm, ← EuclideanSpace.real_norm_sq_eq]
  have hn := diagonalFilteredGraph_mask_norm d p e Ω H bad a R ha hhead htail hΩ
  have hz := matrix_toEuclideanLin_norm_le (spectralMask bad*diagonalFilteredGraph d p e Ω H) z
  rw [Matrix.toLpLin_mul, LinearMap.comp_apply] at hz
  have hb : ‖(spectralMask bad).toEuclideanLin
      ((diagonalFilteredGraph d p e Ω H).toEuclideanLin z)‖ ≤ (ε/10)*‖z‖ :=
    hz.trans (mul_le_mul_of_nonneg_right (hn.trans hsmall) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg z))).mpr hb
  have hc : (ε/10)^2 ≤ ε := by nlinarith
  rw [mul_pow] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖))

end
end HierarchicalAbsoluteSpectral
