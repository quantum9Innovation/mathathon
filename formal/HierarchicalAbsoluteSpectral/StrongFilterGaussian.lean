import HierarchicalAbsoluteSpectral.StrongFilterConstruct
import HierarchicalAbsoluteSpectral.StrongFilterRange

/-!
The full strong Gaussian/Chebyshev capture theorem: actual polynomial,
actual covariance-conditioned random input, finite stopping degree, actual
orthonormal range (including rank loss), and an explicit success probability.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem gaussianCaptureRadius_ge_one (k : ℕ) (U β : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 ≤ gaussianCaptureRadius k U β := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hku : 1 ≤ (k : ℝ)*U := by nlinarith
  have hx : 1 ≤ 100*(k : ℝ)*U/β := by
    apply (le_div_iff₀ hβ).mpr
    nlinarith
  unfold gaussianCaptureRadius
  nlinarith [sq_nonneg (100*(k : ℝ)*U/β-1),
    mul_nonneg (show 0 ≤ 100*(k : ℝ)*U/β-1 by linarith)
      (show 0 ≤ (100*(k : ℝ)*U/β)^2+100*(k : ℝ)*U/β+1 by positivity)]

theorem strongGaussianDenominator_ge_one (k : ℕ) (U β α : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) : 1 ≤ 2*gaussianCaptureRadius k U β/α := by
  have hR := gaussianCaptureRadius_ge_one k U β hk hU hβ hβ1
  apply (le_div_iff₀ hα).mpr
  linarith

def strongGaussianDegree (k : ℕ) (U β α : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) : ℕ :=
  strongFilterDegree α (2*gaussianCaptureRadius k U β/α) hα hα1
    (strongGaussianDenominator_ge_one k U β α hk hU hβ hβ1 hα hα1)

theorem strongGaussianDegree_stops (k : ℕ) (U β α : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    2*gaussianCaptureRadius k U β/α ≤
      strongFilterDenominator α (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1) :=
  strongFilterDegree_stops _ _ _ _ _

theorem strongGaussianDegree_bound (k : ℕ) (U β α : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1 : ℝ) ≤
      2*Real.log (4*gaussianCaptureRadius k U β/α)/Real.sqrt α+1 := by
  have h := strongFilterDegree_bound α (2*gaussianCaptureRadius k U β/α) hα hα1
    (strongGaussianDenominator_ge_one k U β α hk hU hβ hβ1 hα hα1)
  simpa only [strongGaussianDegree,
    show (2 : ℝ)*(2*gaussianCaptureRadius k U β/α) = 4*gaussianCaptureRadius k U β/α by ring] using h

def strongGaussianOutput {k r : ℕ} (T S : Core k) (α : ℝ) (v : ℕ)
    (G : Fin r → Fin k → ℝ) : Matrix (Fin k) (Fin r) ℝ :=
  aeval T (strongFilterPolynomial α v)*(Sᵀ*columnsMatrix G)

def strongGaussianSuccess {k r : ℕ} (T S : Core k) (α : ℝ) (v : ℕ) :
    Set (Fin r → Fin k → ℝ) :=
  {G | ∃ w : ℕ, w ≤ r ∧ ∃ U : Matrix (Fin k) (Fin w) ℝ,
    Uᵀ*U = 1 ∧ ∃ W : Matrix (Fin w) (Fin r) ℝ,
      ∃ X : Matrix (Fin r) (Fin w) ℝ,
        strongGaussianOutput T S α v G = U*W ∧
        U = strongGaussianOutput T S α v G*X ∧
        ‖((1 : Core k)-U*Uᵀ)*T‖ ≤ 1+3*α}

theorem strongGaussianSuccess_of_not_bad {k r : ℕ}
    (T Q S Sinv : Core k) (d : Fin k → ℝ) (hr : r ≤ k)
    (hQ : Qᵀ*Q = 1) (hQQ : Q*Qᵀ = 1) (hdiag : T = Q*Matrix.diagonal d*Qᵀ)
    (hSinv : Sinv*S = 1) (a U β α : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hcond : ‖S‖/a ≤ U) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (v : ℕ) (hden : 2*gaussianCaptureRadius k U β/α ≤ strongFilterDenominator α v)
    (hdlo : ∀ i, 0 ≤ d i) (hdhi : ∀ i, d i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val → d i ≤ 1+α)
    (G : Fin r → Fin k → ℝ)
    (hG : G ∉ gaussianCaptureBad
      ((Q*columnEmbedding (leadingEmbedding hr))ᵀ*Sᵀ) (Function.Embedding.refl (Fin r)) a β) :
    G ∈ strongGaussianSuccess T S α v := by
  let J := Q*columnEmbedding (leadingEmbedding hr)
  let A := Jᵀ*Sᵀ
  let D := Qᵀ*Sᵀ
  let H := gaussianHeadRightInverse A (Function.Embedding.refl (Fin r)) G
  have hDn : ‖D‖ ≤ ‖S‖ := gaussian_rotated_start_norm Q S hQ
  have hcap := gaussian_capture_of_not_bad A D (Function.Embedding.refl (Fin r)) a ‖S‖ U β
    hk hr ha hDn hcond hU hβ hβ1 G hG
  have hhead : (Jᵀ*(Sᵀ*columnsMatrix G))*H = 1 := by
    simpa only [gaussianLinearColumns_matrix, A, H, Matrix.mul_assoc] using hcap.1
  have hgraph : ‖(Qᵀ*(Sᵀ*columnsMatrix G))*H‖ ≤ gaussianCaptureRadius k U β := by
    simpa only [gaussianLinearColumns_matrix, D, H, Matrix.mul_assoc] using hcap.2
  obtain ⟨w,hw,V,hV,W,X,hY,hX⟩ := orthonormal_range_factorization (strongGaussianOutput T S α v G)
  refine ⟨w,hw,V,hV,W,X,hY,hX,?_⟩
  apply chebyshev_strong_filter_from_head_right_inverse T Q d hr hQ hQQ hdiag
    (Sᵀ*columnsMatrix G) H (gaussianCaptureRadius k U β) α
    (by unfold gaussianCaptureRadius; positivity) hα v hdlo hdhi hdtail hden hhead hgraph V W hV hY

/-- Full strong-filter success for the actual conditioned start SᵀXi.
Only deterministic matrix/spectrum bounds are hypotheses. The Gaussian
right inverse, projector approximation and residual are all constructed. -/
theorem gaussian_chebyshev_strong_filter {k r : ℕ}
    (T S Sinv : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r ≤ k)
    (hSinv : Sinv*S = 1) (a U β α : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hcond : ‖S‖/a ≤ U) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hdlo : ∀ i, 0 ≤ strongEigenvalues T hT i)
    (hdhi : ∀ i, strongEigenvalues T hT i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val → strongEigenvalues T hT i ≤ 1+α) :
    (gaussianColumns k r).real
      (strongGaussianSuccess T S α (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1)) ≥ 1-β := by
  let Q := strongSpectralQ T hT
  let J := Q*columnEmbedding (leadingEmbedding hr)
  let A := Jᵀ*Sᵀ
  have hQ : Qᵀ*Q = 1 := strongSpectralQ_gram T hT
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = (columnEmbedding (leadingEmbedding hr))ᵀ*(Qᵀ*Q)*columnEmbedding (leadingEmbedding hr) := by
        simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one]; exact columnEmbedding_gram _
  have hA : ∀ u : Fin r → ℝ, (∑ i, (u i)^2) = 1 → a^2 ≤ ∑ j, (∑ i, A i j*u i)^2 :=
    gaussian_head_covariance_lower J S Sinv hJ hSinv a ha hInv
  have hbad := gaussianCaptureBad_probability A (Function.Embedding.refl (Fin r)) a β hk hr hr ha hβ hβ1 hA
  have hgood : (gaussianColumns k r).real (gaussianCaptureBad A (Function.Embedding.refl (Fin r)) a β)ᶜ ≥ 1-β := by
    rw [measureReal_compl (gaussianCaptureBad_measurable _ _ _ _), probReal_univ]
    linarith
  apply hgood.trans
  exact measureReal_mono (fun G hG => strongGaussianSuccess_of_not_bad
    T Q S Sinv (strongEigenvalues T hT) hr hQ (strongSpectralQ_coGram T hT)
    (strongSpectralQ_diagonalizes T hT) hSinv a U β α hk ha hInv hcond hU hβ hβ1 hα
    (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1)
    (strongGaussianDegree_stops k U β α hk hU hβ hβ1 hα hα1) hdlo hdhi hdtail G hG) (by finiteness)

/-- A measurable success event with the pointwise guarantee. This form is
available even without choosing a measurable orthonormal basis of each
random range. -/
theorem gaussian_chebyshev_strong_filter_good_event {k r : ℕ}
    (T S Sinv : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r ≤ k)
    (hSinv : Sinv*S = 1) (a U β α : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hcond : ‖S‖/a ≤ U) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hdlo : ∀ i, 0 ≤ strongEigenvalues T hT i)
    (hdhi : ∀ i, strongEigenvalues T hT i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val → strongEigenvalues T hT i ≤ 1+α) :
    ∃ E : Set (Fin r → Fin k → ℝ), MeasurableSet E ∧
      (gaussianColumns k r).real E ≥ 1-β ∧
        ∀ G ∈ E, G ∈ strongGaussianSuccess T S α
          (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1) := by
  let Q := strongSpectralQ T hT
  let J := Q*columnEmbedding (leadingEmbedding hr)
  let A := Jᵀ*Sᵀ
  have hQ : Qᵀ*Q = 1 := strongSpectralQ_gram T hT
  have hJ : Jᵀ*J = 1 := by
    calc
      _ = (columnEmbedding (leadingEmbedding hr))ᵀ*(Qᵀ*Q)*columnEmbedding (leadingEmbedding hr) := by
        simp only [J, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one]; exact columnEmbedding_gram _
  have hA : ∀ u : Fin r → ℝ, (∑ i, (u i)^2) = 1 → a^2 ≤ ∑ j, (∑ i, A i j*u i)^2 :=
    gaussian_head_covariance_lower J S Sinv hJ hSinv a ha hInv
  have hbad := gaussianCaptureBad_probability A (Function.Embedding.refl (Fin r)) a β hk hr hr ha hβ hβ1 hA
  refine ⟨(gaussianCaptureBad A (Function.Embedding.refl (Fin r)) a β)ᶜ,
    (gaussianCaptureBad_measurable _ _ _ _).compl, ?_, ?_⟩
  · rw [measureReal_compl (gaussianCaptureBad_measurable _ _ _ _), probReal_univ]
    linarith
  · intro G hG
    exact strongGaussianSuccess_of_not_bad
      T Q S Sinv (strongEigenvalues T hT) hr hQ (strongSpectralQ_coGram T hT)
      (strongSpectralQ_diagonalizes T hT) hSinv a U β α hk ha hInv hcond hU hβ hβ1 hα
      (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1)
      (strongGaussianDegree_stops k U β α hk hU hβ hβ1 hα hα1) hdlo hdhi hdtail G hG

end
end HierarchicalAbsoluteSpectral
