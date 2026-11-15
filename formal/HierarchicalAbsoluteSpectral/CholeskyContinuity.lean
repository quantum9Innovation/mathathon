import HierarchicalAbsoluteSpectral.CholeskyProgram
import Mathlib.Topology.Instances.Matrix

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem continuous_matrix_inverse {X : Type*} [TopologicalSpace X] {n : ℕ}
    (A : X → Core n) (hA : Continuous A) (hdet : ∀ x, (A x).det ≠ 0) :
    Continuous (fun x => (A x)⁻¹) := by
  simpa only [Matrix.inv_def,Ring.inverse_eq_inv] using
    (hA.matrix_det.inv₀ hdet).smul hA.matrix_adjugate

theorem choleskySingleProgram_values (D : Core 1) (hD : D.PosDef) :
    (choleskySingleProgram D hD).eval.upper = Real.sqrt (D 0 0) • 1 ∧
      (choleskySingleProgram D hD).eval.inverse = (Real.sqrt (D 0 0))⁻¹ • 1 := by
  simp only [choleskySingleProgram,eval_bind,eval_pure,certify_eval,eval_sqrt,
    eval_div,one_div,FiniteGramPair.replace]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem choleskyProgram_upper_congr (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} {D E : Core n} (hD : D.PosDef) (hE : E.PosDef) (h : D = E) :
    (choleskyProgram kernels n D hD).eval.upper = (choleskyProgram kernels n E hE).eval.upper := by
  subst E
  rfl

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
      (Matrix.fromBlocks p.upper (choleskyOffDiagonal p D'.toBlocks₁₂) 0 q.upper).submatrix e.symm e.symm := by
  rw [choleskyProgram]
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_pure]
  simp only [certify_eval,ArithmeticKernel.program_eval,
    blockSubProgram_eval,blockScaleProgram_eval,neg_one_smul,FiniteGramPair.cast_upper,
    FiniteGramPair.cast_inverse,FiniteGramPair.reindex,FiniteGramPair.replace,
    choleskyBlockPair,FiniteGramPair.cast_upper,FiniteGramPair.cast_inverse,
    choleskySchur,choleskyOffDiagonal]
  congr 2
  apply choleskyProgram_upper_congr
  simp only [certify_eval,ArithmeticKernel.program_eval,blockSubProgram_eval]

theorem choleskyProgram_continuous {X : Type*} [TopologicalSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    ∀ (n : ℕ) (D : X → Core n) (hD : ∀ x, (D x).PosDef), Continuous D →
      Continuous (fun x => (choleskyProgram kernels n (D x) (hD x)).eval.upper) ∧
      Continuous (fun x => (choleskyProgram kernels n (D x) (hD x)).eval.inverse) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D hD hcont
    rcases n with _ | _ | n
    · simp only [choleskyProgram,eval_pure,choleskyEmpty]
      exact ⟨continuous_const,continuous_const⟩
    · have hs : Continuous (fun x => Real.sqrt (D x 0 0)) :=
        Real.continuous_sqrt.comp (hcont.matrix_elem 0 0)
      have hi := hs.inv₀ (fun x => (Real.sqrt_pos.mpr (hD x).diag_pos).ne')
      constructor
      · have he : (fun x => (choleskyProgram kernels 1 (D x) (hD x)).eval.upper) =
            (fun x => Real.sqrt (D x 0 0) • (1 : Core 1)) :=
          funext (fun x => by rw [choleskyProgram]; exact (choleskySingleProgram_values (D x) (hD x)).1)
        rw [he]
        exact hs.smul continuous_const
      · have he : (fun x => (choleskyProgram kernels 1 (D x) (hD x)).eval.inverse) =
            (fun x => (Real.sqrt (D x 0 0))⁻¹ • (1 : Core 1)) :=
          funext (fun x => by rw [choleskyProgram]; exact (choleskySingleProgram_values (D x) (hD x)).2)
        rw [he]
        exact hi.smul continuous_const
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r,l]; omega
      have he : l+r=n+2 := by dsimp [l,r]; omega
      let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
      let D' := fun x => (D x).submatrix e e
      have hp : ∀ x, (D' x).PosDef := fun x => (hD x).submatrix e.injective
      let A := fun x => (D' x).toBlocks₁₁
      let B := fun x => (D' x).toBlocks₁₂
      let C := fun x => (D' x).toBlocks₂₂
      have hA : ∀ x, (A x).PosDef := fun x => (hp x).submatrix Sum.inl_injective
      let p := fun x => (choleskyProgram kernels l (A x) (hA x)).eval
      have hDcont : Continuous D' := hcont.matrix_submatrix e e
      have hAc : Continuous A := hDcont.matrix_submatrix Sum.inl Sum.inl
      have hBc : Continuous B := hDcont.matrix_submatrix Sum.inl Sum.inr
      have hCc : Continuous C := hDcont.matrix_submatrix Sum.inr Sum.inr
      have hpc := ih l hl A hA hAc
      let H := fun x => choleskyOffDiagonal (p x) (B x)
      have hHc : Continuous H := hpc.2.matrix_transpose.matrix_mul hBc
      let T := fun x => choleskySchur (p x) (B x) (C x)
      have hT : ∀ x, (T x).PosDef := by
        intro x
        exact choleskySchur_posDef (p x) (B x) (C x)
          ((hermitian_block_decomposition (D' x) (hp x).isHermitian).symm ▸ hp x)
      have hTc : Continuous T := hCc.sub (hHc.matrix_transpose.matrix_mul hHc)
      let q := fun x => (choleskyProgram kernels r (T x) (hT x)).eval
      have hqc := ih r hr T hT hTc
      have hu : Continuous (fun x => (choleskyProgram kernels (n+2) (D x) (hD x)).eval.upper) := by
        have hf : (fun x => (choleskyProgram kernels (n+2) (D x) (hD x)).eval.upper) =
            (fun x => (Matrix.fromBlocks (p x).upper (H x) 0 (q x).upper).submatrix e.symm e.symm) :=
          funext (fun x => choleskyProgram_block_values kernels n (D x) (hD x))
        rw [hf]
        exact (hpc.1.matrix_fromBlocks hHc continuous_const hqc.1).matrix_submatrix e.symm e.symm
      refine ⟨hu,?_⟩
      have hf : (fun x => (choleskyProgram kernels (n+2) (D x) (hD x)).eval.inverse) =
          (fun x => (choleskyProgram kernels (n+2) (D x) (hD x)).eval.upper⁻¹) :=
        funext (fun x => (choleskyProgram kernels (n+2) (D x) (hD x)).eval.inverse_eq)
      rw [hf]
      exact continuous_matrix_inverse _ hu (fun x => isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det _).mp (choleskyProgram kernels (n+2) (D x) (hD x)).eval.isUnit))

end
end HierarchicalAbsoluteSpectral
