import HierarchicalAbsoluteSpectral.MainStatementsStrong
import HierarchicalAbsoluteSpectral.StrongFilterFinalBudget
import HierarchicalAbsoluteSpectral.PhysicalPencil

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p k r : ℕ}
attribute [local irreducible] automaticStrongPhysicalRangeProgram

/-- Deterministic correctness of the literal strong-output program on its
constructed physical event. This is a caller lemma for the randomized main
theorem; the main theorem must establish this event and the hierarchy. -/
theorem strongProjectionOutputProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bbar : Matrix (Fin k) (Fin p) ℝ)
    (hsupport : A*B=Z*Bbar) (R Bm Q₀ : Core k)
    (hR : IsUnit R.det) (hBm : Bmᵀ=Bm)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (κ C h θ t U β : ℝ) (hκ : κ ≤ 5) (hC : 1 ≤ C) (hh : 0 < h)
    (hθ : 0 < θ) (hθh : θ ≤ h) (hθ1 : θ ≤ 1) (ht : 0 ≤ t)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hGpos : (Zᵀ*Z).PosDef) (hG : Zᵀ*Z ≤ (2:ℝ) • (1 : Core k))
    (hQ : Q₀ ≤ (2:ℝ) • (Bbar*Bbarᵀ))
    (hmass : Bm ≤ (1+literalFinalMass C θ) • (Zᵀ*Z)⁻¹)
    (hinvariant : inverseMetric R-κ •
      ((t • Bm-Bbar*Bbarᵀ)*(inverseMetric R)⁻¹*(t • Bm-Bbar*Bbarᵀ)) ≤
        (C*h) • (t • (1 : Core k)+Q₀))
    (htail : t ≤ ((1+literalFinalX C h θ)/(1-literalFinalX C h θ))*
      (1/(1-literalFinalMass C θ))*(tailSingularValue (A*B) r)^2)
    (G : Fin r → Fin k → ℝ)
    (hStrong : G ∈ physicalStrongSuccess Z R (t • Bm-Bbar*Bbarᵀ)
      (fun G' => Lmap*(Polynomial.aeval T (strongFilterPolynomial (literalFinalAlpha C h θ)
        (automaticStrongPhysicalRangeProgram kernels PT PL U β (literalFinalAlpha C h θ)
          hk hU hβ hβ1 (literal_final_tolerance_budget C h θ hC hh hθ hθh).alpha_positive
          (by have := (literal_final_tolerance_budget C h θ hC hh hθ hθh).alpha_small; linarith)
          (columnsMatrix G')).eval.1)*columnsMatrix G')) (literalFinalAlpha C h θ)) :
    let result := (strongProjectionOutputProgram kernels A B PT PL U β (literalFinalAlpha C h θ)
      hk hU hβ hβ1 (literal_final_tolerance_budget C h θ hC hh hθ hθh).alpha_positive
      (by have := (literal_final_tolerance_budget C h θ hC hh hθ hθh).alpha_small; linarith)
      (columnsMatrix G)).eval
    result.product.rank ≤ r ∧ ‖A*B-result.product‖ ≤ (1+θ)*tailSingularValue (A*B) r := by
  let hb := literal_final_tolerance_budget C h θ hC hh hθ hθh
  let α := literalFinalAlpha C h θ
  have hα1 : α ≤ 1 := by have := hb.alpha_small; linarith
  let result := (strongProjectionOutputProgram kernels A B PT PL U β α
    hk hU hβ hβ1 hb.alpha_positive hα1 (columnsMatrix G)).eval
  have hc := strongProjectionOutputProgram_dual_certificate kernels A B PT PL U β α
    hk hU hβ hβ1 hb.alpha_positive hα1 Z R (t • Bm-Bbar*Bbarᵀ) G hStrong
  have hphysicalMass := physical_mass_bound Z Bm (literalFinalMass C θ) hb.mass_positive.le hGpos hmass
  have hphysicalD := physical_D_bound Z Bbar Q₀ t ht hG hQ
  have hphysicalIdentity := physical_pencil_identity Z Bbar Bm t
  rw [← hsupport] at hphysicalD hphysicalIdentity
  have hK : (t • Bm-Bbar*Bbarᵀ)ᵀ=t • Bm-Bbar*Bbarᵀ := by
    simp only [Matrix.transpose_sub,Matrix.transpose_smul,hBm,Matrix.transpose_mul,Matrix.transpose_transpose]
  have hs := hierarchical_spectral_error r A B result.left result.width_le hc.1
    Z (inverseMetric R) (t • Bm-Bbar*Bbarᵀ) (t • (1 : Core k)+Q₀) Bm
    κ C h (literalFinalB C h θ) t (literalFinalMass C θ) θ (literalFinalX C h θ)
    (inverseMetric_posDef R hR) hK hb.strong_nonneg (by linarith) hh.le ht hθ.le hθ1
    (hb.relaxation κ hκ) hb.physical_error hb.near_nonneg hb.near_error
    hb.mass_positive.le hb.mass_error hinvariant hphysicalIdentity hphysicalMass hphysicalD hc.2 htail
  have hp := strongProjectionOutputProgram_projected_product kernels A B PT PL U β α
    hk hU hβ hβ1 hb.alpha_positive hα1 (columnsMatrix G)
  change result.product=result.left*(result.leftᵀ*(A*B)) at hp
  change result.product.rank ≤ r ∧ ‖A*B-result.product‖ ≤ _
  rw [hp]
  exact hs

end
end HierarchicalAbsoluteSpectral
