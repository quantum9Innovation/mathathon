import HierarchicalAbsoluteSpectral.StrongFilterPhysical

/-! State conditioned capture directly with the manuscript's spectral
condition-number bound ‖S‖*‖S^-1‖≤U, eliminating the auxiliary covariance
lower-bound parameter from the public physical theorem. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem inverse_spectral_norm_pos {k : ℕ} (S : Core k) (hk : 1 ≤ k) (hS : IsUnit S.det) :
    0 < ‖S⁻¹‖ := by
  have hI : (1 : Core k) ≠ 0 := by
    let i : Fin k := ⟨0,by omega⟩
    intro he
    have hh := congrArg (fun A : Core k => A i i) he
    simpa using hh
  apply norm_pos_iff.mpr
  intro hz
  have he := Matrix.nonsing_inv_mul S hS
  rw [hz, Matrix.zero_mul] at he
  exact hI he.symm

theorem gaussian_chebyshev_physical_condition_number_good_event {n k r : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R₀ S K : Core k)
    (hR₀ : IsUnit R₀.det) (hS : IsUnit S.det) (hK : Kᵀ = K)
    (hT : (filteredOperator (R₀ᵀ*K*R₀) S).toEuclideanLin.IsSymmetric) (hr : r ≤ k)
    (U β α : ℝ) (hk : 1 ≤ k) (hcond : ‖S‖*‖S⁻¹‖ ≤ U)
    (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdlo : ∀ i, 0 ≤ strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i)
    (hdhi : ∀ i, strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i ≤ 2)
    (hdtail : ∀ i, r ≤ i.val →
      strongEigenvalues (filteredOperator (R₀ᵀ*K*R₀) S) hT i ≤ 1+α) :
    ∃ E : Set (Fin r → Fin k → ℝ), MeasurableSet E ∧
      (gaussianColumns k r).real E ≥ 1-β ∧
        ∀ G ∈ E, G ∈ physicalStrongSuccess Z (R₀*S) K
          (carriedPhysicalOutput Z R₀ S K α
            (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1)) α := by
  let a : ℝ := 1/‖S⁻¹‖
  have ha : 0 < a := by dsimp [a]; exact one_div_pos.mpr (inverse_spectral_norm_pos S hk hS)
  have hInv : ‖S⁻¹‖ ≤ 1/a := by simp [a]
  have hcond' : ‖S‖/a ≤ U := by simpa [a, div_eq_mul_inv] using hcond
  exact gaussian_chebyshev_physical_good_event Z R₀ S K hR₀ hS hK hT hr a U β α hk ha hInv
    hcond' hU hβ hβ1 hα hα1 hdlo hdhi hdtail

end
end HierarchicalAbsoluteSpectral
