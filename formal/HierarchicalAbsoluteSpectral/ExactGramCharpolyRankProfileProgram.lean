import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileScalar

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def fieldPrincipalAssembleProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {l r : ℕ} {A : Core l} {S : Core r} (p : FieldOrderedPSDPrincipalData A)
    (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C)
    (H : Matrix (Fin p.dimension) (Fin r) ℝ)
    (hH : H = p.inverse * B.submatrix p.selected id) :
    ArithmeticProgram (FieldOrderedPSDPrincipalData ((Matrix.fromBlocks A B Bᵀ C).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm)) := do
  let N ← certify (blockScaleProgram (-1) (H.submatrix id q.selected))
  let ec : Fin (p.dimension + q.dimension) ≃ Fin p.dimension ⊕ Fin q.dimension := finSumFinEquiv.symm
  let er : Fin (l+r) ≃ Fin l ⊕ Fin r := finSumFinEquiv.symm
  let P := (Matrix.fromBlocks 1 N.val 0 1).submatrix ec ec
  let J := (Matrix.fromBlocks p.inverse 0 0 q.inverse).submatrix ec ec
  let F := (Matrix.fromBlocks p.coordinates H 0 q.coordinates).submatrix ec er
  let PJ ← certify (rankProfileMulProgram kernels P J)
  let Jout ← certify (rankProfileMulProgram kernels PJ.val Pᵀ)
  let Rout ← certify (rankProfileMulProgram kernels P F)
  have hN : N.val = -(H.submatrix id q.selected) := by
    simp only [N.property, blockScaleProgram_eval, neg_one_smul]
  let expected := p.block B C hD q hS
  have hR : Rout.val = expected.coordinates := by
    rw [Rout.property, rankProfileMulProgram_eval]
    dsimp only [P, F]
    rw [hN, hH, Matrix.submatrix_mul_equiv]
    rfl
  have hJ : Jout.val = expected.inverse := by
    rw [Jout.property, rankProfileMulProgram_eval, PJ.property, rankProfileMulProgram_eval]
    dsimp only [P, J]
    rw [hN, hH]
    change ((Matrix.fromBlocks 1 _ 0 1).submatrix ec ec *
      (Matrix.fromBlocks p.inverse 0 0 q.inverse).submatrix ec ec) *
        (Matrix.fromBlocks 1 _ 0 1)ᵀ.submatrix ec ec = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  ArithmeticProgram.pure (expected.replace Rout.val Jout.val hR hJ)

theorem fieldPrincipalAssembleProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {l r : ℕ} {A : Core l} {S : Core r} (p : FieldOrderedPSDPrincipalData A)
    (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C)
    (H : Matrix (Fin p.dimension) (Fin r) ℝ) (hH : H = p.inverse * B.submatrix p.selected id) :
    (fieldPrincipalAssembleProgram kernels p B C hD q hS H hH).admissible := by
  simp only [fieldPrincipalAssembleProgram, admissible_bind, certify_admissible,
    blockScaleProgram_admissible, rankProfileMulProgram_admissible, admissible_pure, and_self]

theorem fieldPrincipalAssembleProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {l r : ℕ} {A : Core l} {S : Core r} (p : FieldOrderedPSDPrincipalData A)
    (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C)
    (H : Matrix (Fin p.dimension) (Fin r) ℝ) (hH : H = p.inverse * B.submatrix p.selected id) :
    (fieldPrincipalAssembleProgram kernels p B C hD q hS H hH).work ≤
      3 * kernelEnvelope kernels (l+r) + p.dimension * q.dimension := by
  have hp : p.dimension ≤ l := by simpa only [Fintype.card_fin] using p.dimension_le
  have hq : q.dimension ≤ r := by simpa only [Fintype.card_fin] using q.dimension_le
  have hk : p.dimension + q.dimension ≤ l+r := Nat.add_le_add hp hq
  simp only [fieldPrincipalAssembleProgram, work_bind, certify_work,
    blockScaleProgram_work, work_pure]
  calc
    _ ≤ p.dimension * q.dimension + (kernelEnvelope kernels (l+r) +
        (kernelEnvelope kernels (l+r) + (kernelEnvelope kernels (l+r) + 0))) := by
      gcongr
      all_goals apply rankProfileMulProgram_work_le <;> omega
    _ = _ := by omega

def fieldPrincipalProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    (w : ℕ) → (D : Core w) → D.PosSemidef → ArithmeticProgram (FieldOrderedPSDPrincipalData D)
  | 0, D, _ => ArithmeticProgram.pure (fieldPrincipalEmpty D)
  | 1, D, hD => fieldPrincipalSingleProgram D hD
  | w+2, D, hD => by
    let l := (w+2)/2
    let r := w+2-l
    have hl : l < w+2 := by dsimp [l]; omega
    have hr : r < w+2 := by dsimp [r,l]; omega
    have he : l+r = w+2 := by dsimp [l,r]; omega
    let e : Fin l ⊕ Fin r ≃ Fin (w+2) := finSumFinEquiv.trans (finCongr he)
    let D' := D.submatrix e e
    have hp : D'.PosSemidef := hD.submatrix e
    have hb := hermitian_block_decomposition D' hp.isHermitian
    have hA : D'.toBlocks₁₁.PosSemidef := hp.submatrix Sum.inl
    exact do
      let p ← fieldPrincipalProgram kernels l D'.toBlocks₁₁ hA
      let H ← certify (rankProfileMulProgram kernels p.inverse (D'.toBlocks₁₂.submatrix p.selected id))
      have hH : H.val = p.inverse * D'.toBlocks₁₂.submatrix p.selected id := by
        rw [H.property, rankProfileMulProgram_eval]
      let Q ← certify (rankProfileMulProgram kernels (D'.toBlocks₁₂.submatrix p.selected id)ᵀ H.val)
      let S ← certify (blockSubProgram D'.toBlocks₂₂ Q.val)
      have hS : S.val = p.schur D'.toBlocks₁₂ D'.toBlocks₂₂ := by
        simp only [S.property, blockSubProgram_eval, Q.property, rankProfileMulProgram_eval,
          hH, FieldPSDPrincipalData.schur]
      have hSpos : S.val.PosSemidef := by
        rw [hS]
        exact p.schur_posSemidef D'.toBlocks₁₂ D'.toBlocks₂₂ (hb.symm ▸ hp)
      let q ← fieldPrincipalProgram kernels r S.val hSpos
      let out ← fieldPrincipalAssembleProgram kernels p D'.toBlocks₁₂ D'.toBlocks₂₂
        (hb.symm ▸ hp) q hS H.val hH
      let converted := out.reindexSize he
      ArithmeticProgram.pure (converted.cast (by
        ext i j
        change (Matrix.fromBlocks D'.toBlocks₁₁ D'.toBlocks₁₂ D'.toBlocks₁₂ᵀ
          D'.toBlocks₂₂) (e.symm i) (e.symm j) = D i j
        have hh := congrArg (fun M => M (e.symm i) (e.symm j)) hb
        simpa only [D', Matrix.submatrix_apply, Equiv.apply_symm_apply] using hh))
termination_by w => w
decreasing_by all_goals assumption

theorem fieldPrincipalProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (w : ℕ) (D : Core w) (hD : D.PosSemidef) :
    (fieldPrincipalProgram kernels w D hD).admissible := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    rcases w with _ | _ | w
    · rw [fieldPrincipalProgram]; trivial
    · rw [fieldPrincipalProgram]; exact fieldPrincipalSingleProgram_admissible D hD
    · have hl : (w+2)/2 < w+2 := by omega
      have hr : w+2-(w+2)/2 < w+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [fieldPrincipalProgram]
      simp only [admissible_bind, certify_admissible, rankProfileMulProgram_admissible,
        blockSubProgram_admissible, fieldPrincipalAssembleProgram_admissible,
        admissible_pure, ihl, ihr, and_self]

def fieldColumnRankProfileProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) : ArithmeticProgram (FieldColumnRankProfile V) := do
  let D ← certify (rankProfileMulProgram kernels Vᵀ V)
  have hD : D.val = Vᵀ * V := D.property.trans (rankProfileMulProgram_eval _ _ _)
  have hp : D.val.PosSemidef := by
    rw [hD]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self V
  let p ← fieldPrincipalProgram kernels w D.val hp
  let U ← certify (rankProfileMulProgram kernels p.inverse (V.submatrix id p.selected)ᵀ)
  ArithmeticProgram.pure (fieldColumnRankProfileOfGram V p hD U.val
    (U.property.trans (rankProfileMulProgram_eval _ _ _)))

theorem fieldColumnRankProfileProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ) :
    (fieldColumnRankProfileProgram kernels V).admissible := by
  simp only [fieldColumnRankProfileProgram, admissible_bind, certify_admissible,
    rankProfileMulProgram_admissible, fieldPrincipalProgram_admissible,
    admissible_pure, and_self]

end
end HierarchicalAbsoluteSpectral
