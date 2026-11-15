import HierarchicalAbsoluteSpectral.StrongFilterGaussian

/-! The strong certificate for the actual carried physical range, with
dependent columns removed and no inverse of a fine polynomial applied. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator

def carriedPhysicalOutput {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R₀ S K : Core k) (α : ℝ) (v : ℕ)
    (G : Fin r → Fin k → ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  Z*((R₀⁻¹)ᵀ*(aeval (carriedOperator (R₀ᵀ*K*R₀) S) (strongFilterPolynomial α v)*columnsMatrix G))

def physicalStrongSuccess {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R K : Core k)
    (Y : (Fin r → Fin k → ℝ) → Matrix (Fin n) (Fin r) ℝ) (α : ℝ) :
    Set (Fin r → Fin k → ℝ) :=
  {G | ∃ w : ℕ, w ≤ r ∧ ∃ V : Matrix (Fin n) (Fin w) ℝ,
    Vᵀ*V = 1 ∧ ∃ B : Matrix (Fin w) (Fin r) ℝ,
      ∃ C : Matrix (Fin r) (Fin w) ℝ, Y G = V*B ∧ V = Y G*C ∧
        ∀ x : Fin n → ℝ, Vᵀ *ᵥ x = 0 →
          quadratic (K*(inverseMetric R)⁻¹*K) (Zᵀ *ᵥ x)-2*quadratic K (Zᵀ *ᵥ x) ≤
            ((1+3*α)^2-1)*quadratic (inverseMetric R) (Zᵀ *ᵥ x)}

theorem physicalStrongSuccess_of_core {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R K T S : Core k) (α : ℝ) (hα : 0 ≤ α) (v : ℕ)
    (hR : IsUnit R.det) (hK : Kᵀ = K) (hT : T = 1-normalizedPencil R K)
    (G : Fin r → Fin k → ℝ) (hG : G ∈ strongGaussianSuccess T S α v) :
    G ∈ physicalStrongSuccess Z R K
      (fun G => Z*((R⁻¹)ᵀ*strongGaussianOutput T S α v G)) α := by
  obtain ⟨u,hu,U,hU,W,X,hY,hX,hres⟩ := hG
  let L := Z*(R⁻¹)ᵀ
  obtain ⟨w,hw,V,hV,B,C,hL,hC⟩ := orthonormal_range_factorization (L*U)
  refine ⟨w,hw.trans hu,V,hV,B*W,X*C,?_,?_,?_⟩
  · change Z*((R⁻¹)ᵀ*strongGaussianOutput T S α v G) = V*(B*W)
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, show Z*(R⁻¹)ᵀ = L from rfl, hL, Matrix.mul_assoc]
  · change V = Z*((R⁻¹)ᵀ*strongGaussianOutput T S α v G)*(X*C)
    rw [hC, hX]
    simp only [L, Matrix.mul_assoc]
  · intro x hx
    have hres' : ‖(1-U*Uᵀ)*(1-normalizedPencil R K)‖ ≤ 1+3*α := by rwa [hT] at hres
    exact physical_strong_action_certificate Z R K U V B (1+3*α) hR hK
      (by linarith) hL hres' x hx

theorem carriedPhysicalOutput_eq_lift {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R₀ S K : Core k) (hS : IsUnit S.det)
    (α : ℝ) (v : ℕ) (G : Fin r → Fin k → ℝ) :
    carriedPhysicalOutput Z R₀ S K α v G =
      Z*(((R₀*S)⁻¹)ᵀ*strongGaussianOutput (filteredOperator (R₀ᵀ*K*R₀) S) S α v G) := by
  unfold carriedPhysicalOutput strongGaussianOutput
  exact (exact_physical_lift Z R₀ S (R₀ᵀ*K*R₀) hS (strongFilterPolynomial α v) (columnsMatrix G)).symm

theorem gaussian_chebyshev_physical_strong_certificate {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R₀ S K : Core k)
    (hR₀ : IsUnit R₀.det) (hS : IsUnit S.det) (hK : Kᵀ = K)
    (hT : (filteredOperator (R₀ᵀ*K*R₀) S).toEuclideanLin.IsSymmetric) (hr : r ≤ k)
    (a U β α : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (hInv : ‖S⁻¹‖ ≤ 1/a)
    (hcond : ‖S‖/a ≤ U) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hdlo : ∀ i, 0 ≤ strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i)
    (hdhi : ∀ i, strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val →
      strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i ≤ 1+α) :
    (gaussianColumns k r).real (physicalStrongSuccess Z (R₀*S) K
      (carriedPhysicalOutput Z R₀ S K α (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1)) α) ≥ 1-β := by
  let T := filteredOperator (R₀ᵀ*K*R₀) S
  let v := strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1
  have hcore := gaussian_chebyshev_strong_filter T S S⁻¹ hT hr
    (Matrix.nonsing_inv_mul S hS) a U β α hk ha hInv hcond hU hβ hβ1 hα hα1 hdlo hdhi hdtail
  have hR : IsUnit (R₀*S).det := by rw [Matrix.det_mul]; exact hR₀.mul hS
  have hTdef : T = 1-normalizedPencil (R₀*S) K := by
    simp only [T, filteredOperator, normalizedPencil, Matrix.transpose_mul, Matrix.mul_assoc]
  apply hcore.trans
  apply measureReal_mono ?_ (by finiteness)
  intro G hG
  have hp := physicalStrongSuccess_of_core Z (R₀*S) K T S α hα.le v hR hK hTdef G hG
  have heq : carriedPhysicalOutput (r := r) Z R₀ S K α v =
      (fun G : Fin r → Fin k → ℝ => Z*(((R₀*S)⁻¹)ᵀ*strongGaussianOutput T S α v G)) := by
    funext G
    exact carriedPhysicalOutput_eq_lift Z R₀ S K hS α v G
  rw [heq]
  exact hp

end
end HierarchicalAbsoluteSpectral
