import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLBlock

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix

theorem leadingPrincipal_comp {n : ℕ} (D : Core n) (r : ℕ) (hr : r ≤ n)
    (s : ℕ) (hs : s ≤ r) :
    leadingPrincipal (leadingPrincipal D r hr) s hs = leadingPrincipal D s (hs.trans hr) := by
  rfl

theorem LeadingPrincipalRegular.leading {n r : ℕ} {D : Core n}
    (hD : LeadingPrincipalRegular D) (hr : r ≤ n) :
    LeadingPrincipalRegular (leadingPrincipal D r hr) := by
  intro s hs
  rw [leadingPrincipal_comp]
  exact hD s (hs.trans hr)

theorem split_topLeft_eq_leading {n l r : ℕ} (D : Core n) (he : l+r = n) :
    (D.submatrix (finSumFinEquiv.trans (finCongr he))
      (finSumFinEquiv.trans (finCongr he))).toBlocks₁₁ = leadingPrincipal D l (by omega) := by
  ext i j
  rfl

theorem leading_schur_regular {n l r : ℕ} (D : Core n) (hD : D.IsHermitian)
    (hReg : LeadingPrincipalRegular D) (he : l+r = n)
    (left : RegularCongruenceData (D.submatrix (finSumFinEquiv.trans (finCongr he))
      (finSumFinEquiv.trans (finCongr he))).toBlocks₁₁) :
    LeadingPrincipalRegular (regularBlockSchur left
      (D.submatrix (finSumFinEquiv.trans (finCongr he))
        (finSumFinEquiv.trans (finCongr he))).toBlocks₁₂
      (D.submatrix (finSumFinEquiv.trans (finCongr he))
        (finSumFinEquiv.trans (finCongr he))).toBlocks₂₂) := by
  let e : Fin l ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr he)
  let D' := D.submatrix e e
  let A := D'.toBlocks₁₁
  let B := D'.toBlocks₁₂
  let C := D'.toBlocks₂₂
  have hRegA : LeadingPrincipalRegular A := by
    rw [show A = leadingPrincipal D l (by omega) from split_topLeft_eq_leading D he]
    exact hReg.leading (by omega)
  letI := ((Matrix.isUnit_iff_isUnit_det A).mpr hRegA.isUnit_det).invertible
  have hb := hermitian_block_decomposition D' (hD.submatrix e)
  intro s hs
  let f : Fin s ↪ Fin r := Fin.castLEEmb hs
  let Bs := B.submatrix id f
  let Cs := C.submatrix f f
  let fs : Fin l ⊕ Fin s → Fin l ⊕ Fin r := Sum.map id f
  have hBlock : Matrix.fromBlocks A Bs Bsᵀ Cs = D'.submatrix fs fs := by
    calc
      _ = (Matrix.fromBlocks A B Bᵀ C).submatrix fs fs := by
        ext i j
        cases i <;> cases j <;> rfl
      _ = _ := congrArg (fun M : Matrix (Fin l ⊕ Fin r) (Fin l ⊕ Fin r) ℝ => M.submatrix fs fs) hb
  have hSelected : D'.submatrix fs fs =
      (leadingPrincipal D (l+s) (by omega)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext i j
    change D (e (fs i)) (e (fs j)) =
      D ((Fin.castLEEmb (show l+s ≤ n by omega)) (finSumFinEquiv i))
        ((Fin.castLEEmb (show l+s ≤ n by omega)) (finSumFinEquiv j))
    cases i <;> cases j <;> rfl
  have hUnit : IsUnit (Matrix.fromBlocks A Bs Bsᵀ Cs).det := by
    rw [hBlock,hSelected,Matrix.det_submatrix_equiv_self]
    exact hReg (l+s) (by omega)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hUnit
  have hPrefix : leadingPrincipal (regularBlockSchur left B C) s hs = Cs-Bsᵀ*A⁻¹*Bs := by
    have hi : left.inverseMatrix = A⁻¹ := left.inverseMatrix_eq_inv
    change leadingPrincipal (C-Bᵀ*(left.inverseMatrix*B)) s hs = Cs-Bsᵀ*A⁻¹*Bs
    rw [hi]
    ext i j
    simp only [leadingPrincipal,
      Matrix.mul_assoc, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Bs,Cs,A,B,C,D',e,f,Matrix.of_apply,Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, id_eq]
  change IsUnit (leadingPrincipal (regularBlockSchur left B C) s hs).det
  rw [hPrefix]
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz,mul_zero] at hUnit
  exact (not_isUnit_zero hUnit)

end
end HierarchicalAbsoluteSpectral
