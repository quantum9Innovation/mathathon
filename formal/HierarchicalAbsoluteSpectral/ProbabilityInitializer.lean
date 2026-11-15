import HierarchicalAbsoluteSpectral.ProbabilityInitializerBounds
import HierarchicalAbsoluteSpectral.StrongFilterGaussian

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def initializerResidual {k w : ℕ} (T : Core k) (U : Matrix (Fin k) (Fin w) ℝ) : Core k :=
  T-U*(Uᵀ*T)

def initializerValue {k w : ℕ} (T : Core k) (U : Matrix (Fin k) (Fin w) ℝ) : ℝ :=
  matrixFrobeniusValue (initializerResidual T U)

def initializerRatio (k : ℕ) (β : ℝ) : ℝ := Real.sqrt k*(1+gaussianCaptureRadius k 1 β)

theorem initializerResidual_eq {k w : ℕ} (T : Core k) (U : Matrix (Fin k) (Fin w) ℝ) :
    initializerResidual T U = ((1 : Core k)-U*Uᵀ)*T := by
  simp [initializerResidual, Matrix.sub_mul, Matrix.mul_assoc]

theorem initializerRatio_pos (k : ℕ) (β : ℝ) (hk : 1 ≤ k) (hβ : 0 < β) :
    0 < initializerRatio k β := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  unfold initializerRatio gaussianCaptureRadius
  positivity

theorem initializer_zero_rank {k r w : ℕ}
    (T : Core k) (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r)
    (hzero : initializerValue T U = 0) :
    T = U*(Uᵀ*T) ∧ T.rank ≤ r := by
  have hz : initializerResidual T U = 0 := (matrixFrobeniusValue_eq_zero_iff _).mp hzero
  have hT : T = U*(Uᵀ*T) := sub_eq_zero.mp hz
  exact ⟨hT, by rw [hT]; exact (Matrix.rank_mul_le_left _ _).trans U.rank_le_width |>.trans hw⟩

/-- A fresh Gaussian range sketch gives a polynomial-ratio bracket for the
actual r-th sorted eigenvalue. The quantified basis may be the output of
the counted range algorithm, including rank loss. Zero target eigenvalues
force an exactly zero computed residual on the same event. -/
theorem gaussian_initializer_good_event {k r : ℕ}
    (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r < k)
    (hd : ∀ i, 0 ≤ strongEigenvalues T hT i)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ E : Set (Fin r → Fin k → ℝ), MeasurableSet E ∧
      (gaussianColumns k r).real E ≥ 1-β ∧
        ∀ G ∈ E, ∀ w : ℕ, w ≤ r → ∀ U : Matrix (Fin k) (Fin w) ℝ,
          Uᵀ*U = 1 → ∀ W : Matrix (Fin w) (Fin r) ℝ, T*columnsMatrix G = U*W →
            strongEigenvalues T hT ⟨r,hr⟩ ≤ initializerValue T U ∧
            initializerValue T U ≤ initializerRatio k β*strongEigenvalues T hT ⟨r,hr⟩ := by
  let Q := strongSpectralQ T hT
  let J := Q*columnEmbedding (leadingEmbedding hr.le)
  let A := Jᵀ
  have hk : 1 ≤ k := by omega
  have hQ : Qᵀ*Q = 1 := strongSpectralQ_gram T hT
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = (columnEmbedding (leadingEmbedding hr.le))ᵀ*(Qᵀ*Q)*columnEmbedding (leadingEmbedding hr.le) := by
        simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one]; exact columnEmbedding_gram _
  have hA : ∀ u : Fin r → ℝ, (∑ i, (u i)^2) = 1 →
      (1 : ℝ)^2 ≤ ∑ j, (∑ i, A i j*u i)^2 := by
    intro u hu
    simpa only [Matrix.transpose_one, Matrix.mul_one] using
      gaussian_head_covariance_lower J (1 : Core k) 1 hJ (by simp) 1 (by norm_num)
        (by simpa using matrix_identity_norm_le_one k) u hu
  have hDn : ‖Qᵀ‖ ≤ 1 := by
    rw [spectral_norm_transpose]
    exact orthonormal_columns_norm_le_one Q hQ
  have hbad := gaussianCaptureBad_probability A (Function.Embedding.refl (Fin r)) 1 β
    hk hr.le hr.le (by norm_num) hβ hβ1 hA
  refine ⟨(gaussianCaptureBad A (Function.Embedding.refl (Fin r)) 1 β)ᶜ,
    (gaussianCaptureBad_measurable _ _ _ _).compl, ?_, ?_⟩
  · rw [measureReal_compl (gaussianCaptureBad_measurable _ _ _ _), probReal_univ]
    linarith
  · intro G hG w hw U hU W hspan
    let H := gaussianHeadRightInverse A (Function.Embedding.refl (Fin r)) G
    have hcap := gaussian_capture_of_not_bad A Qᵀ (Function.Embedding.refl (Fin r)) 1 1 1 β
      hk hr.le (by norm_num) hDn (by norm_num) (by norm_num) hβ hβ1 G hG
    have hhead : (Jᵀ*columnsMatrix G)*H = 1 := by
      simpa only [gaussianLinearColumns_matrix, A, H] using hcap.1
    have hgraph : ‖(Qᵀ*columnsMatrix G)*H‖ ≤ gaussianCaptureRadius k 1 β := by
      simpa only [gaussianLinearColumns_matrix, H] using hcap.2
    have htail : ∀ i : Fin k, r ≤ i.val → |strongEigenvalues T hT i| ≤ strongEigenvalues T hT ⟨r,hr⟩ := by
      intro i hi
      rw [abs_of_nonneg (hd i)]
      exact hT.eigenvalues_antitone (by simp) (show (⟨r,hr⟩ : Fin k) ≤ i from hi)
    have hupp := gaussian_range_residual_upper T Q (strongEigenvalues T hT) hr.le hQ
      (strongSpectralQ_coGram T hT) (strongSpectralQ_diagonalizes T hT)
      (columnsMatrix G) H (strongEigenvalues T hT ⟨r,hr⟩) (gaussianCaptureRadius k 1 β)
      (hd _) (by unfold gaussianCaptureRadius; positivity) htail hhead hgraph U W hU hspan
    constructor
    · exact (projection_residual_ge_eigenvalue T hT hr U hw).trans
        (by simpa only [initializerValue, initializerResidual_eq] using
          spectral_norm_le_matrixFrobeniusValue (initializerResidual T U))
    · calc
        _ ≤ Real.sqrt k*‖initializerResidual T U‖ := matrixFrobeniusValue_le_cols_sqrt_mul_norm _
        _ ≤ Real.sqrt k*((1+gaussianCaptureRadius k 1 β)*strongEigenvalues T hT ⟨r,hr⟩) := by
          rw [initializerResidual_eq]
          exact mul_le_mul_of_nonneg_left hupp (Real.sqrt_nonneg _)
        _ = _ := by unfold initializerRatio; ring

theorem initializer_bracket_of_bounds {k w : ℕ}
    (T : Core k) (U : Matrix (Fin k) (Fin w) ℝ) (β ell : ℝ)
    (hk : 1 ≤ k) (hβ : 0 < β) (hell : 0 < ell)
    (hlo : ell ≤ initializerValue T U)
    (hhi : initializerValue T U ≤ initializerRatio k β*ell) :
    0 < initializerValue T U/initializerRatio k β ∧
      initializerValue T U/initializerRatio k β ≤ ell ∧ ell ≤ initializerValue T U ∧
      initializerValue T U/(initializerValue T U/initializerRatio k β) = initializerRatio k β := by
  have hC := initializerRatio_pos k β hk hβ
  have ht : 0 < initializerValue T U := hell.trans_le hlo
  refine ⟨by positivity, (div_le_iff₀ hC).mpr (by nlinarith), hlo, ?_⟩
  field_simp

end
end HierarchicalAbsoluteSpectral
