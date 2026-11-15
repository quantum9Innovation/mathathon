import HierarchicalAbsoluteSpectral.ThresholdKrylovProgram
import HierarchicalAbsoluteSpectral.GaussianConditioning

set_option backward.isDefEq.respectTransparency false

/-! Covariance-conditioned Gaussian guarantee for the actually computed
Krylov compression. The exceptional set is explicit and measurable. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ENNReal
variable {k h r : ℕ}

theorem columnEmbedding_transpose_mul_rows (e : Fin h ↪ Fin k)
    (M : Matrix (Fin k) (Fin r) ℝ) :
    (columnEmbedding e)ᵀ*M = M.submatrix e id := by
  ext i c
  simp [columnEmbedding, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.one_apply, ite_mul]

theorem gaussianCaptureRadius_ge_one (k : ℕ) (U β : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ' : β ≤ 1) :
    1 ≤ gaussianCaptureRadius k U β := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hc : 1 ≤ 100*k*U/β := by
    apply (le_div_iff₀ hβ).mpr
    nlinarith
  exact one_le_pow₀ hc

def computedKrylovRitzValue (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (G : Fin r → Fin k → ℝ) (j : Fin k) : ℝ :=
  thresholdRitzValue T hT
    (krylovQueryDataProgram kernels T hT actions q (Sᵀ*columnsMatrix G)).eval.range.basis j

theorem computedKrylovRitzValue_always_safe (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (G : Fin r → Fin k → ℝ) (j : Fin k) :
    computedKrylovRitzValue kernels T hT.isHermitian actions q S G j ≤
      (orderedEigenvalue T hT.isHermitian j)^2 := by
  exact thresholdRitzValue_always_safe T hT
    (krylovQueryDataProgram kernels T hT.isHermitian actions q (Sᵀ*columnsMatrix G)).eval.range.basis
    (krylovQueryDataProgram kernels T hT.isHermitian actions q (Sᵀ*columnsMatrix G)).eval.range.orthogonal j

def krylovCaptureBad (T : Core k) (hT : T.IsHermitian) (S : Core k) (j : Fin k) (a β : ℝ) :
    Set (Fin (j.val+1) → Fin k → ℝ) :=
  gaussianCaptureBad
    (((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT))ᵀ*Sᵀ).submatrix
      (krylovHeadEmbedding j) id)
    (Function.Embedding.refl (Fin (j.val+1))) a β

theorem krylovCaptureBad_measurable (T : Core k) (hT : T.IsHermitian) (S : Core k)
    (j : Fin k) (a β : ℝ) : MeasurableSet (krylovCaptureBad T hT S j a β) :=
  gaussianCaptureBad_measurable _ _ _ _

theorem krylov_head_covariance (T : Core k) (hT : T.IsHermitian) (S Sinv : Core k)
    (hSinv : Sinv*S = 1) (j : Fin k) (a : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (u : Fin (j.val+1) → ℝ) (hu : ∑ i, (u i)^2 = 1) :
    a^2 ≤ ∑ c, (∑ i,
      (((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT))ᵀ*Sᵀ).submatrix
        (krylovHeadEmbedding j) id) i c*u i)^2 := by
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT
  let Q := strongSpectralQ T hs
  let e := krylovHeadEmbedding j
  let J := Q*columnEmbedding e
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = (columnEmbedding e)ᵀ*(Qᵀ*Q)*columnEmbedding e := by
        simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [strongSpectralQ_gram T hs, Matrix.mul_one, columnEmbedding_gram]
  have heq : Jᵀ*Sᵀ = (Qᵀ*Sᵀ).submatrix e id := by
    calc
      _ = (columnEmbedding e)ᵀ*(Qᵀ*Sᵀ) := by simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := columnEmbedding_transpose_mul_rows e _
  have hh := gaussian_head_covariance_lower J S Sinv hJ hSinv a ha hInv u hu
  simpa only [heq] using hh

theorem krylovCaptureBad_probability (T : Core k) (hT : T.IsHermitian) (S Sinv : Core k)
    (hSinv : Sinv*S = 1) (j : Fin k) (a β : ℝ) (ha : 0 < a)
    (hInv : ‖Sinv‖ ≤ 1/a) (hβ : 0 < β) (hβ' : β ≤ 1) :
    (gaussianColumns k (j.val+1)).real (krylovCaptureBad T hT S j a β) ≤ β := by
  have hdim : j.val+1 ≤ k := Nat.succ_le_of_lt j.isLt
  apply gaussianCaptureBad_probability
    (((strongSpectralQ T (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT))ᵀ*Sᵀ).submatrix
      (krylovHeadEmbedding j) id) (Function.Embedding.refl _) a β
    (by omega) hdim hdim ha hβ hβ'
  exact krylov_head_covariance T hT S Sinv hSinv j a ha hInv

theorem computedKrylovRitzValue_of_not_bad
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (S : Core k) (j : Fin k) (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (a b U β ε : ℝ) (ha : 0 < a) (hS : ‖S‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) (q : ℕ)
    (hstop : 10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100) q)
    (G : Fin (j.val+1) → Fin k → ℝ) (hG : G ∉ krylovCaptureBad T hT.isHermitian S j a β) :
    (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 ≤
      computedKrylovRitzValue kernels T hT.isHermitian actions q S G j := by
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian
  let Q := strongSpectralQ T hs
  let D := Qᵀ*Sᵀ
  let e := krylovHeadEmbedding j
  let A := D.submatrix e id
  let H := gaussianHeadRightInverse A (Function.Embedding.refl (Fin (j.val+1))) G
  have hdim : j.val+1 ≤ k := Nat.succ_le_of_lt j.isLt
  have hD : ‖D‖ ≤ b := (gaussian_rotated_start_norm Q S (strongSpectralQ_gram T hs)).trans hS
  have hc := gaussian_capture_of_not_bad A D (Function.Embedding.refl _) a b U β
    (by omega) hdim ha hD hba hU hβ hβ' G hG
  have hhead : ((Qᵀ*(Sᵀ*columnsMatrix G)).submatrix e id)*H = 1 := by
    rw [← Matrix.mul_assoc]
    rw [Matrix.submatrix_mul _ _ e id id Function.bijective_id]
    simpa only [Matrix.submatrix_id_id, gaussianLinearColumns_matrix] using hc.1
  have hnorm : ‖(Qᵀ*(Sᵀ*columnsMatrix G))*H‖ ≤ gaussianCaptureRadius k U β := by
    rw [← Matrix.mul_assoc]
    change ‖(D*columnsMatrix G)*H‖ ≤ gaussianCaptureRadius k U β
    simpa only [gaussianLinearColumns_matrix] using hc.2
  exact computed_thresholdRitzValue_of_capture kernels T hT actions j htarget ε
    (gaussianCaptureRadius k U β) hε hε'
    (gaussianCaptureRadius_ge_one k U β (by omega) hU hβ hβ') q hstop
    (Sᵀ*columnsMatrix G) H hhead hnorm

theorem computedKrylovRitzValue_success_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (S Sinv : Core k) (hSinv : Sinv*S = 1) (j : Fin k)
    (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (a b U β ε : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hS : ‖S‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) (q : ℕ)
    (hstop : 10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100) q) :
    (gaussianColumns k (j.val+1)).real {G |
      (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 ≤
        computedKrylovRitzValue kernels T hT.isHermitian actions q S G j} ≥ 1-β := by
  have hbad := krylovCaptureBad_probability T hT.isHermitian S Sinv hSinv j a β ha hInv hβ hβ'
  have hgood : (gaussianColumns k (j.val+1)).real
      (krylovCaptureBad T hT.isHermitian S j a β)ᶜ ≥ 1-β := by
    rw [measureReal_compl (krylovCaptureBad_measurable T hT.isHermitian S j a β), probReal_univ]
    linarith
  apply hgood.trans
  exact measureReal_mono (fun G hG => computedKrylovRitzValue_of_not_bad kernels T hT actions S j
    htarget a b U β ε ha hS hba hU hβ hβ' hε hε' q hstop G hG) (by finiteness)

end
end HierarchicalAbsoluteSpectral
