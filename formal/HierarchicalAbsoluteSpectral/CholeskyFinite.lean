import HierarchicalAbsoluteSpectral.CholeskyBlock
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite, balanced recursive Gram factor and inverse. No spectral
decomposition or matrix square-root operation occurs in the construction. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

namespace FiniteGramPair

def reindex {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {D : Matrix n n ℝ} (p : FiniteGramPair D) (e : m ≃ n) :
    FiniteGramPair (D.submatrix e e) where
  upper := p.upper.submatrix e e
  inverse := p.inverse.submatrix e e
  gram := by
    change p.upperᵀ.submatrix e e*p.upper.submatrix e e = D.submatrix e e
    rw [Matrix.submatrix_mul_equiv, p.gram]
  left_inverse := by
    rw [Matrix.submatrix_mul_equiv, p.left_inverse, Matrix.submatrix_one_equiv]
  right_inverse := by
    rw [Matrix.submatrix_mul_equiv, p.right_inverse, Matrix.submatrix_one_equiv]

def cast {n : Type} [Fintype n] [DecidableEq n] {D E : Matrix n n ℝ}
    (p : FiniteGramPair D) (h : D = E) : FiniteGramPair E := h ▸ p

end FiniteGramPair

def choleskyEmpty (D : Core 0) : FiniteGramPair D where
  upper := 1
  inverse := 1
  gram := Subsingleton.elim _ _
  left_inverse := by simp
  right_inverse := by simp

def choleskySingle (D : Core 1) (hD : D.PosDef) : FiniteGramPair D := by
  let d := D 0 0
  have hd : 0 < d := hD.diag_pos
  have hr : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : d • (1 : Core 1) = D := by
    ext i j
    fin_cases i
    fin_cases j
    simp [d]
  refine ⟨Real.sqrt d • 1, (Real.sqrt d)⁻¹ • 1, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul, ← pow_two, Real.sq_sqrt hd.le]
    exact he
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hr, one_smul]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hr, one_smul]

theorem hermitian_block_decomposition {m n : Type} [Fintype m] [Fintype n]
    (D : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hD : D.IsHermitian) :
    Matrix.fromBlocks D.toBlocks₁₁ D.toBlocks₁₂ D.toBlocks₁₂ᵀ D.toBlocks₂₂ = D := by
  have ht : Dᵀ = D := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq
  ext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => exact congrArg (fun A => A (Sum.inr i) (Sum.inl j)) ht
    | inr j => rfl

def finiteCholesky : (n : ℕ) → (D : Core n) → D.PosDef → FiniteGramPair D
  | 0, D, _ => choleskyEmpty D
  | 1, D, hD => choleskySingle D hD
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
    let p := finiteCholesky l D'.toBlocks₁₁ hA
    have hSchur : (choleskySchur p D'.toBlocks₁₂ D'.toBlocks₂₂).PosDef :=
      choleskySchur_posDef p D'.toBlocks₁₂ D'.toBlocks₂₂ (hb.symm ▸ hp)
    let q := finiteCholesky r (choleskySchur p D'.toBlocks₁₂ D'.toBlocks₂₂) hSchur
    let pair := (choleskyBlockPair p D'.toBlocks₁₂ D'.toBlocks₂₂ q).cast hb
    refine (pair.reindex e.symm).cast ?_
    ext i j
    simp [D', Matrix.submatrix_apply]
termination_by n => n
decreasing_by all_goals assumption

theorem finiteCholesky_gram (n : ℕ) (D : Core n) (hD : D.PosDef) :
    (finiteCholesky n D hD).upperᵀ*(finiteCholesky n D hD).upper = D :=
  (finiteCholesky n D hD).gram

theorem finiteCholesky_inverse (n : ℕ) (D : Core n) (hD : D.PosDef) :
    (finiteCholesky n D hD).inverse = (finiteCholesky n D hD).upper⁻¹ :=
  (finiteCholesky n D hD).inverse_eq

end
end HierarchicalAbsoluteSpectral
