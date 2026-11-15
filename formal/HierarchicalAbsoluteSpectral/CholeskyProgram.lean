import HierarchicalAbsoluteSpectral.CholeskyFinite
import HierarchicalAbsoluteSpectral.ArithmeticKernel

/-! Executed scalar arithmetic for balanced Cholesky and its inverse factor.
Every multiplication uses a verified arithmetic kernel. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

namespace FiniteGramPair

@[simp] theorem cast_upper {n : Type} [Fintype n] [DecidableEq n]
    {D E : Matrix n n ℝ} (p : FiniteGramPair D) (h : D = E) :
    (p.cast h).upper = p.upper := by cases h; rfl

@[simp] theorem cast_inverse {n : Type} [Fintype n] [DecidableEq n]
    {D E : Matrix n n ℝ} (p : FiniteGramPair D) (h : D = E) :
    (p.cast h).inverse = p.inverse := by cases h; rfl

def replace {n : Type} [Fintype n] [DecidableEq n] {D : Matrix n n ℝ}
    (p : FiniteGramPair D) (U V : Matrix n n ℝ) (hU : U = p.upper) (hV : V = p.inverse) :
    FiniteGramPair D where
  upper := U
  inverse := V
  gram := by rw [hU]; exact p.gram
  left_inverse := by rw [hU, hV]; exact p.left_inverse
  right_inverse := by rw [hU, hV]; exact p.right_inverse

end FiniteGramPair

def choleskySingleProgram (D : Core 1) (hD : D.PosDef) : ArithmeticProgram (FiniteGramPair D) := do
  let s ← certify (ArithmeticProgram.sqrt (D 0 0))
  let v ← certify (ArithmeticProgram.div 1 s.val)
  have hs : s.val = Real.sqrt (D 0 0) := s.property
  have hv : v.val = (Real.sqrt (D 0 0))⁻¹ := by
    rw [v.property, eval_div, hs, one_div]
  ArithmeticProgram.pure ((choleskySingle D hD).replace
    (Matrix.diagonal (fun _ => s.val)) (Matrix.diagonal (fun _ => v.val))
    (by rw [hs]; ext i j; fin_cases i; fin_cases j; simp [choleskySingle])
    (by rw [hv]; ext i j; fin_cases i; fin_cases j; simp [choleskySingle]))

theorem choleskySingleProgram_work (D : Core 1) (hD : D.PosDef) :
    (choleskySingleProgram D hD).work = 2 := by
  simp only [choleskySingleProgram, work_bind, certify_work, work_sqrt, work_div, work_pure]

theorem choleskySingleProgram_admissible (D : Core 1) (hD : D.PosDef) :
    (choleskySingleProgram D hD).admissible := by
  simp only [choleskySingleProgram, admissible_bind, certify_admissible,
    admissible_div, certify_eval, eval_sqrt, admissible_pure, and_true]
  constructor
  · exact (certify_admissible _).mpr ((admissible_sqrt _).mpr hD.diag_pos.le)
  · exact (Real.sqrt_pos.mpr hD.diag_pos).ne'

def choleskyProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    (n : ℕ) → (D : Core n) → D.PosDef → ArithmeticProgram (FiniteGramPair D)
  | 0, D, _ => ArithmeticProgram.pure (choleskyEmpty D)
  | 1, D, hD => choleskySingleProgram D hD
  | n+2, D, hD => by
    let l := (n+2)/2
    let r := n+2-l
    have hl : l < n+2 := by dsimp [l]; omega
    have hr : r < n+2 := by dsimp [r, l]; omega
    have he : l+r = n+2 := by dsimp [l, r]; omega
    let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
    let D' := D.submatrix e e
    have hp : D'.PosDef := hD.submatrix e.injective
    have hb := hermitian_block_decomposition D' hp.isHermitian
    have hA : D'.toBlocks₁₁.PosDef := hp.submatrix Sum.inl_injective
    exact do
      let p ← choleskyProgram kernels l D'.toBlocks₁₁ hA
      let H ← certify ((kernels l l r).program p.inverseᵀ D'.toBlocks₁₂)
      have hH : H.val = choleskyOffDiagonal p D'.toBlocks₁₂ :=
        H.property.trans ((kernels l l r).program_eval _ _)
      let R ← certify ((kernels r l r).program H.valᵀ H.val)
      let T ← certify (blockSubProgram D'.toBlocks₂₂ R.val)
      have hT : T.val = choleskySchur p D'.toBlocks₁₂ D'.toBlocks₂₂ := by
        rw [T.property, blockSubProgram_eval, R.property, ArithmeticKernel.program_eval, hH]
        rfl
      have hTpos : T.val.PosDef := by
        rw [hT]
        exact choleskySchur_posDef p D'.toBlocks₁₂ D'.toBlocks₂₂ (hb.symm ▸ hp)
      let q ← choleskyProgram kernels r T.val hTpos
      let L ← certify ((kernels l l r).program p.inverse H.val)
      let W ← certify ((kernels l r r).program L.val q.inverse)
      let N ← certify (blockScaleProgram (-1) W.val)
      let qc := q.cast hT
      have hN : N.val = -(p.inverse*choleskyOffDiagonal p D'.toBlocks₁₂*qc.inverse) := by
        simp only [N.property, blockScaleProgram_eval, W.property, ArithmeticKernel.program_eval,
          L.property, hH, qc, FiniteGramPair.cast_inverse, neg_one_smul]
      let expected := choleskyBlockPair p D'.toBlocks₁₂ D'.toBlocks₂₂ qc
      let raw := expected.replace
        (Matrix.fromBlocks p.upper H.val 0 q.upper)
        (Matrix.fromBlocks p.inverse N.val 0 q.inverse)
        (by dsimp [expected, choleskyBlockPair]; simp only [hH, qc, FiniteGramPair.cast_upper])
        (by dsimp [expected, choleskyBlockPair]; rw [hN]; simp [qc])
      let pair := raw.cast hb
      ArithmeticProgram.pure ((pair.reindex e.symm).cast (by
        ext i j
        simp [D', Matrix.submatrix_apply]))
termination_by n => n
decreasing_by all_goals assumption

def choleskyCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n+2 =>
    let l := (n+2)/2
    let r := n+2-l
    choleskyCost kernels l+choleskyCost kernels r+
      2*(kernels l l r).cost+(kernels r l r).cost+(kernels l r r).cost+r*r+l*r
termination_by n => n
decreasing_by all_goals dsimp; omega

theorem choleskyProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.PosDef) : (choleskyProgram kernels n D hD).admissible := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [choleskyProgram]; trivial
    · rw [choleskyProgram]; exact choleskySingleProgram_admissible D hD
    · have hl : (n+2)/2 < n+2 := by omega
      have hr : n+2-(n+2)/2 < n+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [choleskyProgram]
      simp only [admissible_bind, certify_admissible, ArithmeticKernel.program_admissible,
        blockSubProgram_admissible, blockScaleProgram_admissible, admissible_pure, ihl, ihr,
        and_self]

theorem choleskyProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.PosDef) :
    (choleskyProgram kernels n D hD).work = choleskyCost kernels n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [choleskyProgram, choleskyCost]; rfl
    · rw [choleskyProgram, choleskyCost]; exact choleskySingleProgram_work D hD
    · have hl : (n+2)/2 < n+2 := by omega
      have hr : n+2-(n+2)/2 < n+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [choleskyProgram, choleskyCost]
      simp only [work_bind, certify_work, ArithmeticKernel.program_work,
        blockSubProgram_work, blockScaleProgram_work, work_pure, ihl, ihr]
      omega

theorem choleskyProgram_correct (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.PosDef) :
    let p := (choleskyProgram kernels n D hD).eval
    p.upperᵀ*p.upper = D ∧ p.inverse*p.upper = 1 ∧ p.upper*p.inverse = 1 := by
  exact ⟨(choleskyProgram kernels n D hD).eval.gram,
    (choleskyProgram kernels n D hD).eval.left_inverse,
    (choleskyProgram kernels n D hD).eval.right_inverse⟩

end
end HierarchicalAbsoluteSpectral
