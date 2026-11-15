import HierarchicalAbsoluteSpectral.FiniteHierarchy
import HierarchicalAbsoluteSpectral.StrongFilterFinalBudget
import HierarchicalAbsoluteSpectral.RuntimeFamilyOverhead

/-! Identify the executed hierarchy's constants with the scalar constants
appearing in the manuscript, final tolerance budget and family estimates. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

theorem hierarchyConstant_eq_defectConstant (L : ℕ) : hierarchyConstant L = defectConstant L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [hierarchyConstant,defectConstant,ih]

theorem accuracyScale_eq_hierarchyConstant (L : ℕ) :
    accuracyScale L = 1000000*(hierarchyConstant L+1) := by
  rw [hierarchyConstant_eq_defectConstant]
  rfl

theorem hierarchy_literal_final_budget (L : ℕ) (h θ : ℝ)
    (hh : 0 < h) (hθ : 0 < θ) (hθh : θ ≤ h) :
    LiteralFinalBudget (hierarchyConstant L) h θ :=
  literal_final_tolerance_budget _ h θ (hierarchyConstant_ge_one L) hh hθ hθh

theorem hierarchy_final_alpha_eq (L : ℕ) (h θ : ℝ) :
    literalFinalAlpha (hierarchyConstant L) h θ = θ/(accuracyScale L*h) := by
  rw [accuracyScale_eq_hierarchyConstant]
  rfl

theorem hierarchy_final_mass_eq (L : ℕ) (θ : ℝ) :
    literalFinalMass (hierarchyConstant L) θ = θ/accuracyScale L := by
  rw [accuracyScale_eq_hierarchyConstant]
  rfl

end
end HierarchicalAbsoluteSpectral
