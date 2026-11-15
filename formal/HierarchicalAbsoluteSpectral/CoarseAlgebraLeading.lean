import HierarchicalAbsoluteSpectral.MatrixInequalities

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

def leadingPrincipal {n : ℕ} (D : Core n) (r : ℕ) (hr : r ≤ n) : Core r :=
  D.submatrix (Fin.castLEEmb hr) (Fin.castLEEmb hr)

def LeadingPrincipalRegular {n : ℕ} (D : Core n) : Prop :=
  ∀ (r : ℕ) (hr : r ≤ n), IsUnit (leadingPrincipal D r hr).det

theorem LeadingPrincipalRegular.isUnit_det {n : ℕ} {D : Core n}
    (hD : LeadingPrincipalRegular D) : IsUnit D.det := by
  have hd := hD n le_rfl
  simpa [leadingPrincipal] using hd

end
end HierarchicalAbsoluteSpectral
