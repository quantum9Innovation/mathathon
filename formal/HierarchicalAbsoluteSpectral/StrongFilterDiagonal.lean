import HierarchicalAbsoluteSpectral.StrongFilterScalar
import HierarchicalAbsoluteSpectral.GaussianConditioning
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Actual sorted spectral coordinates and polynomial diagonalization. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def strongSpectralBasis {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)) :=
  hT.eigenvectorBasis (by simp)

def strongEigenvalues {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) : Fin k → ℝ :=
  hT.eigenvalues (by simp)

def strongSpectralQ {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) : Core k :=
  fun i j => strongSpectralBasis T hT j i

theorem strongSpectralQ_gram {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    (strongSpectralQ T hT)ᵀ*strongSpectralQ T hT = 1 := by
  ext i j
  have h := (orthonormal_iff_ite.mp (strongSpectralBasis T hT).orthonormal) i j
  simpa only [strongSpectralQ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

theorem strongSpectralQ_coGram {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    strongSpectralQ T hT*(strongSpectralQ T hT)ᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp (strongSpectralQ_gram T hT)

theorem strongSpectralQ_intertwines {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    T*strongSpectralQ T hT = strongSpectralQ T hT*Matrix.diagonal (strongEigenvalues T hT) := by
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v i)
    (hT.apply_eigenvectorBasis (by simp) j)
  simpa only [Matrix.mul_diagonal, Matrix.mul_apply, strongSpectralQ,
    strongSpectralBasis, strongEigenvalues, Matrix.toEuclideanLin_apply,
    ofLp_toLp, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_comm,
    RCLike.ofReal_real_eq_id, id_eq] using h

theorem strongSpectralQ_diagonalizes {k : ℕ} (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) :
    T = strongSpectralQ T hT*Matrix.diagonal (strongEigenvalues T hT)*(strongSpectralQ T hT)ᵀ := by
  rw [← strongSpectralQ_intertwines, Matrix.mul_assoc, strongSpectralQ_coGram, Matrix.mul_one]

theorem aeval_diagonal_real {k : ℕ} (d : Fin k → ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.eval_add, Matrix.diagonal_add]
  | monomial n c =>
      simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Polynomial.eval_monomial,
        Matrix.diagonal_pow, Matrix.smul_mul, Matrix.one_mul]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij, smul_eq_mul]

theorem aeval_orthogonal_diagonal {k : ℕ} (T Q : Core k) (d : Fin k → ℝ)
    (hQQ : Q*Qᵀ = 1) (hTQ : T*Q = Q*Matrix.diagonal d) (p : ℝ[X]) :
    aeval T p = Q*Matrix.diagonal (fun i => p.eval (d i))*Qᵀ := by
  rw [← aeval_diagonal_real]
  have hp := polynomial_intertwining T (Matrix.diagonal d) Q hTQ p
  calc
    _ = (aeval T p*Q)*Qᵀ := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    _ = _ := by rw [hp]

theorem orthogonal_diagonal_norm_le {k : ℕ} (Q : Core k) (hQ : Qᵀ*Q = 1)
    (d : Fin k → ℝ) (c : ℝ) (hc : 0 ≤ c) (hd : ∀ i, |d i| ≤ c) :
    ‖Q*Matrix.diagonal d*Qᵀ‖ ≤ c := by
  have hQn := orthonormal_columns_norm_le_one Q hQ
  have hDn : ‖Matrix.diagonal d‖ ≤ c := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hc).mpr (fun i => by simpa [Real.norm_eq_abs] using hd i)
  calc
    _ ≤ (‖Q‖*‖Matrix.diagonal d‖)*‖Qᵀ‖ := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*c)*1 := by rw [spectral_norm_transpose]; gcongr
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
