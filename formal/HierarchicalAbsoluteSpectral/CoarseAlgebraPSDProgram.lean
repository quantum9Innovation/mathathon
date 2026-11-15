import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDBlock
import HierarchicalAbsoluteSpectral.CholeskyProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

namespace PSDGramPair

def replace {n : Type} [Fintype n] [DecidableEq n] {D : Matrix n n ℝ}
    (p : PSDGramPair D) (L : Matrix n (Fin p.dimension) ℝ)
    (U : Matrix (Fin p.dimension) n ℝ) (hL : L = p.factor) (hU : U = p.leftInverse) :
    PSDGramPair D where
  dimension := p.dimension
  dimension_le := p.dimension_le
  factor := L
  leftInverse := U
  gram := by rw [hL]; exact p.gram
  left_inverse := by rw [hL, hU]; exact p.left_inverse

end PSDGramPair

def finiteGramPairToPSD {n : ℕ} {D : Core n} (p : FiniteGramPair D) : PSDGramPair D where
  dimension := n
  dimension_le := by simp
  factor := p.upperᵀ
  leftInverse := p.inverseᵀ
  gram := by simpa only [Matrix.transpose_transpose] using p.gram
  left_inverse := by
    rw [← Matrix.transpose_mul, p.right_inverse, Matrix.transpose_one]

def psdEmpty (D : Core 0) : PSDGramPair D where
  dimension := 0
  dimension_le := by simp
  factor := 0
  leftInverse := 0
  gram := Subsingleton.elim _ _
  left_inverse := Subsingleton.elim _ _

def psdZeroSingle (D : Core 1) (hd : D 0 0 = 0) : PSDGramPair D where
  dimension := 0
  dimension_le := by simp
  factor := 0
  leftInverse := 0
  gram := by
    simp only [Matrix.zero_mul]
    ext i j
    fin_cases i
    fin_cases j
    exact hd.symm
  left_inverse := Subsingleton.elim _ _

theorem single_posDef_of_diag_pos (D : Core 1) (hd : 0 < D 0 0) : D.PosDef := by
  have he : D 0 0 • (1 : Core 1) = D := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [← he]
  exact Matrix.PosDef.one.smul hd

def psdSingleProgram (D : Core 1) (hD : D.PosSemidef) : ArithmeticProgram (PSDGramPair D) :=
  .branch (D 0 0) 0
    (fun hzero => ArithmeticProgram.pure (psdZeroSingle D (le_antisymm hzero hD.diag_nonneg)))
    (fun hpos => do
      let p ← choleskySingleProgram D (single_posDef_of_diag_pos D (lt_of_not_ge hpos))
      ArithmeticProgram.pure (finiteGramPairToPSD p))

theorem psdSingleProgram_admissible (D : Core 1) (hD : D.PosSemidef) :
    (psdSingleProgram D hD).admissible := by
  by_cases hz : D 0 0 ≤ 0
  · simp only [psdSingleProgram, admissible, dif_pos hz]
  · simp only [psdSingleProgram, admissible, dif_neg hz, admissible_bind,
      choleskySingleProgram_admissible, admissible_pure, and_self]

theorem psdSingleProgram_work (D : Core 1) (hD : D.PosSemidef) :
    (psdSingleProgram D hD).work ≤ 3 := by
  simp only [psdSingleProgram, work]
  split_ifs
  · norm_num [work]
  · simp only [work_bind, choleskySingleProgram_work, work_pure]
    norm_num

def psdGramProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    (n : ℕ) → (D : Core n) → D.PosSemidef → ArithmeticProgram (PSDGramPair D)
  | 0, D, _ => ArithmeticProgram.pure (psdEmpty D)
  | 1, D, hD => psdSingleProgram D hD
  | n+2, D, hD => by
    let l := (n+2)/2
    let r := n+2-l
    have hl : l < n+2 := by dsimp [l]; omega
    have hr : r < n+2 := by dsimp [r, l]; omega
    have he : l+r = n+2 := by dsimp [l, r]; omega
    let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
    let D' := D.submatrix e e
    have hp : D'.PosSemidef := hD.submatrix e
    have hb := hermitian_block_decomposition D' hp.isHermitian
    have hA : D'.toBlocks₁₁.PosSemidef := hp.submatrix Sum.inl
    exact do
      let p ← psdGramProgram kernels l D'.toBlocks₁₁ hA
      let H ← certify ((kernels p.dimension l r).program p.leftInverse D'.toBlocks₁₂)
      have hH : H.val = p.leftInverse*D'.toBlocks₁₂ :=
        H.property.trans (ArithmeticKernel.program_eval _ _ _)
      let R ← certify ((kernels r p.dimension r).program H.valᵀ H.val)
      let T ← certify (blockSubProgram D'.toBlocks₂₂ R.val)
      have hT : T.val = psdSchur p D'.toBlocks₁₂ D'.toBlocks₂₂ := by
        simp only [T.property, blockSubProgram_eval, R.property, ArithmeticKernel.program_eval,
          hH, psdSchur]
      have hTpos : T.val.PosSemidef := by
        rw [hT]
        exact psdSchur_posSemidef p D'.toBlocks₁₂ D'.toBlocks₂₂ (hb.symm ▸ hp)
      let q ← psdGramProgram kernels r T.val hTpos
      let V ← certify ((kernels q.dimension r p.dimension).program q.leftInverse H.valᵀ)
      let W ← certify ((kernels q.dimension p.dimension l).program V.val p.leftInverse)
      let N ← certify (blockScaleProgram (-1) W.val)
      have hN : N.val = -(q.leftInverse*(p.leftInverse*D'.toBlocks₁₂)ᵀ*p.leftInverse) := by
        simp only [N.property, blockScaleProgram_eval, W.property, V.property,
          ArithmeticKernel.program_eval, hH, neg_one_smul]
      let expected := psdBlockPairOfEq p D'.toBlocks₁₂ D'.toBlocks₂₂ (hb.symm ▸ hp) q hT
      let ec : Fin (p.dimension+q.dimension) ≃ Fin p.dimension ⊕ Fin q.dimension := finSumFinEquiv.symm
      let rawL := (Matrix.fromBlocks p.factor 0 H.valᵀ q.factor).submatrix id ec
      let rawU := (Matrix.fromBlocks p.leftInverse 0 N.val q.leftInverse).submatrix ec id
      let raw := expected.replace rawL rawU
        (by dsimp [expected, rawL, psdBlockPairOfEq, ec]; simp only [hH])
        (by dsimp [expected, rawU, psdBlockPairOfEq, ec]; simp only [hN])
      let pair := raw.cast hb
      ArithmeticProgram.pure ((pair.reindex e.symm).cast (by
        ext i j
        simp [D', Matrix.submatrix_apply]))
termination_by n => n
decreasing_by all_goals assumption

theorem psdGramProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.PosSemidef) : (psdGramProgram kernels n D hD).admissible := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [psdGramProgram]; trivial
    · rw [psdGramProgram]; exact psdSingleProgram_admissible D hD
    · have hl : (n+2)/2 < n+2 := by omega
      have hr : n+2-(n+2)/2 < n+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [psdGramProgram]
      simp only [admissible_bind, certify_admissible, ArithmeticKernel.program_admissible,
        blockSubProgram_admissible, blockScaleProgram_admissible, admissible_pure, ihl, ihr,
        and_self]

end
end HierarchicalAbsoluteSpectral
