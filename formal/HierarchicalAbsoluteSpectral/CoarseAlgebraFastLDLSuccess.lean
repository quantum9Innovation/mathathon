import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraLeadingSplit

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem fastInertiaProgram_success (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (hReg : LeadingPrincipalRegular D) :
    ∃ out, (fastInertiaProgram kernels n D hD).eval = some out := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [fastInertiaProgram]; exact ⟨_,rfl⟩
    · have hd : D 0 0 ≠ 0 := by
        intro hz
        exact (isUnit_iff_ne_zero.mp hReg.isUnit_det) ((Matrix.det_fin_one D).trans hz)
      rw [fastInertiaProgram,regularSingleProgram,eval_bind]
      cases hs : (finiteNonzeroSearchProgram (fun _ : Fin 1 => D 0 0)).eval with
      | found i hi => exact ⟨_,rfl⟩
      | zero hz => exact False.elim (hd (hz 0))
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r,l]; omega
      have he : l+r = n+2 := by dsimp [l,r]; omega
      let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
      let D' := D.submatrix e e
      have hHerm : D.IsHermitian := by simpa only [Matrix.IsHermitian,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hD
      have hp : D'.IsHermitian := hHerm.submatrix e
      have hA : D'.toBlocks₁₁ᵀ = D'.toBlocks₁₁ := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.toBlocks₁₁,Matrix.submatrix]
          using (hp.submatrix Sum.inl).eq
      have hC : D'.toBlocks₂₂ᵀ = D'.toBlocks₂₂ := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.toBlocks₂₂,Matrix.submatrix]
          using (hp.submatrix Sum.inr).eq
      have hRegA : LeadingPrincipalRegular D'.toBlocks₁₁ := by
        rw [show D'.toBlocks₁₁ = leadingPrincipal D l (by omega) from split_topLeft_eq_leading D he]
        exact hReg.leading (by omega)
      obtain ⟨left,hLeft⟩ := ih l hl D'.toBlocks₁₁ hA hRegA
      let invD := (certify (diagonalInverseProgram left.diagonal)).eval
      let A1 := (certify ((kernels l l l).program left.basis invD.val)).eval
      let Ai := (certify ((kernels l l l).program A1.val left.basisᵀ)).eval
      have hAi : Ai.val = left.inverseMatrix := by
        dsimp [Ai,A1,invD]
        simp only [certify_eval,ArithmeticKernel.program_eval,diagonalInverseProgram_eval,
          RegularCongruenceData.inverseMatrix]
      let W := (certify ((kernels l l r).program Ai.val D'.toBlocks₁₂)).eval
      have hW : W.val = left.inverseMatrix*D'.toBlocks₁₂ := by
        dsimp [W]
        simp only [certify_eval,ArithmeticKernel.program_eval,hAi]
      let R := (certify ((kernels r l r).program D'.toBlocks₁₂ᵀ W.val)).eval
      let T := (certify (blockSubProgram D'.toBlocks₂₂ R.val)).eval
      have hT : T.val = regularBlockSchur left D'.toBlocks₁₂ D'.toBlocks₂₂ := by
        dsimp [T,R]
        simp only [certify_eval,blockSubProgram_eval,ArithmeticKernel.program_eval,hW,regularBlockSchur]
      have hTsym : T.valᵀ = T.val := by
        rw [hT]
        simp only [regularBlockSchur,Matrix.transpose_sub,Matrix.transpose_mul,
          Matrix.transpose_transpose,Matrix.diagonal_transpose,hC,left.inverseMatrix_transpose,Matrix.mul_assoc]
      have hRegT : LeadingPrincipalRegular T.val := by
        rw [hT]
        exact leading_schur_regular D hHerm hReg he left
      obtain ⟨right,hRight⟩ := ih r hr T.val hTsym hRegT
      rw [fastInertiaProgram]
      rw [eval_bind,hLeft]
      rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,hRight]
      rw [eval_bind,eval_bind,eval_bind,eval_pure]
      exact ⟨_,rfl⟩

theorem fastInertiaDiagonalProgram_success (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (hReg : LeadingPrincipalRegular D) :
    ∃ out, (fastInertiaDiagonalProgram kernels n D hD).eval = some out := by
  obtain ⟨out,ho⟩ := fastInertiaProgram_success kernels n D hD hReg
  simp only [fastInertiaDiagonalProgram,eval_bind,ho,eval_pure,Option.map_some]
  exact ⟨_,rfl⟩

end
end HierarchicalAbsoluteSpectral
