import HierarchicalAbsoluteSpectral.CholeskyProgram
import Mathlib.Topology.Instances.Matrix

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem choleskySingleProgram_values (D : Core 1) (hD : D.PosDef) :
    (choleskySingleProgram D hD).eval.upper = Real.sqrt (D 0 0) • 1 ∧
      (choleskySingleProgram D hD).eval.inverse = (Real.sqrt (D 0 0))⁻¹ • 1 := by
  simp only [choleskySingleProgram,eval_bind,eval_pure,certify_eval,eval_sqrt,
    eval_div,one_div,FiniteGramPair.replace]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem choleskyProgram_block_values
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (n : ℕ)
    (D : Core (n+2)) (hD : D.PosDef) :
    let l := (n+2)/2
    let r := n+2-l
    let he : l+r=n+2 := by dsimp [l,r]; omega
    let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
    let D' := D.submatrix e e
    let hp : D'.PosDef := hD.submatrix e.injective
    let hb := hermitian_block_decomposition D' hp.isHermitian
    let p := (choleskyProgram kernels l D'.toBlocks₁₁ (hp.submatrix Sum.inl_injective)).eval
    let T := choleskySchur p D'.toBlocks₁₂ D'.toBlocks₂₂
    let hT : T.PosDef := choleskySchur_posDef p _ _ (hb.symm ▸ hp)
    let q := (choleskyProgram kernels r T hT).eval
    (choleskyProgram kernels (n+2) D hD).eval.upper =
      (Matrix.fromBlocks p.upper (choleskyOffDiagonal p D'.toBlocks₁₂) 0 q.upper).submatrix e.symm e.symm ∧
    (choleskyProgram kernels (n+2) D hD).eval.inverse =
      (Matrix.fromBlocks p.inverse (-(p.inverse*choleskyOffDiagonal p D'.toBlocks₁₂*q.inverse))
        0 q.inverse).submatrix e.symm e.symm := by
  rw [choleskyProgram]
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_pure]
  simp only [certify_eval,ArithmeticKernel.program_eval,
    blockSubProgram_eval,blockScaleProgram_eval,neg_one_smul,FiniteGramPair.cast_upper,
    FiniteGramPair.cast_inverse,FiniteGramPair.reindex,FiniteGramPair.replace,
    choleskyBlockPair,FiniteGramPair.cast_upper,FiniteGramPair.cast_inverse,
    choleskySchur,choleskyOffDiagonal]
  constructor <;> simp only [Matrix.neg_mul,Matrix.mul_assoc]

end
end HierarchicalAbsoluteSpectral
