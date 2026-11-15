import HierarchicalAbsoluteSpectral.CholeskyBlock
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Rank-revealing positive-semidefinite Gram factorization. Zero pivots
are deflated exactly; the rectangular factor has an explicit left inverse. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

structure PSDGramPair (D : Matrix n n ℝ) where
  dimension : ℕ
  dimension_le : dimension ≤ Fintype.card n
  factor : Matrix n (Fin dimension) ℝ
  leftInverse : Matrix (Fin dimension) n ℝ
  gram : factor*factorᵀ = D
  left_inverse : leftInverse*factor = 1

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem psd_congruence_zero_mul_zero (D : Matrix n n ℝ) (hD : D.PosSemidef)
    (Z : Matrix n m ℝ) (hz : Zᵀ*D*Z = 0) : D*Z = 0 := by
  ext i j
  have hscalar : star (Zᵀ j) ⬝ᵥ (D *ᵥ (Zᵀ j)) = 0 := by
    have he := congrArg (fun M => M j j) hz
    rw [Matrix.mul_assoc] at he
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using he
  have hv := (hD.dotProduct_mulVec_zero_iff (Zᵀ j)).mp hscalar
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i

theorem psd_offDiagonal_range {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) :
    p.factor*(p.leftInverse*B) = B := by
  let P : Matrix m m ℝ := 1-p.factor*p.leftInverse
  have hPA : P*A = 0 := by
    calc
      _ = (1-p.factor*p.leftInverse)*(p.factor*p.factorᵀ) := congrArg (P*·) p.gram.symm
      _ = p.factor*p.factorᵀ-p.factor*((p.leftInverse*p.factor)*p.factorᵀ) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [p.left_inverse]; simp
  let Z : Matrix (m ⊕ n) m ℝ := Matrix.fromRows Pᵀ 0
  have hz : Zᵀ*Matrix.fromBlocks A B Bᵀ C*Z = 0 := by
    dsimp only [Z]
    rw [Matrix.transpose_fromRows, Matrix.transpose_transpose, Matrix.transpose_zero,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, hPA]
  have hDZ := psd_congruence_zero_mul_zero _ hD Z hz
  have hB : Bᵀ*Pᵀ = 0 := by
    ext i j
    have he := congrArg (fun M => M (Sum.inr i) j) hDZ
    simpa only [Z, Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero, add_zero,
      Matrix.fromRows_apply_inr, Matrix.zero_apply] using he
  have hPB : P*B = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hB
  dsimp [P] at hPB
  rw [Matrix.sub_mul, Matrix.one_mul] at hPB
  simpa only [Matrix.mul_assoc] using (sub_eq_zero.mp hPB).symm

def psdSchur {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ) : Matrix n n ℝ :=
  C-(p.leftInverse*B)ᵀ*(p.leftInverse*B)

theorem psdSchur_posSemidef {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) : (psdSchur p B C).PosSemidef := by
  let H := p.leftInverse*B
  let Z : Matrix (m ⊕ n) n ℝ := Matrix.fromRows (-(p.leftInverseᵀ*H)) 1
  have hz := hD.conjTranspose_mul_mul_same Z
  have hVA : p.leftInverse*A = p.factorᵀ := by
    calc
      _ = p.leftInverse*(p.factor*p.factorᵀ) := congrArg (p.leftInverse*·) p.gram.symm
      _ = p.factorᵀ := by rw [← Matrix.mul_assoc, p.left_inverse]; simp
  have heq : Zᵀ*Matrix.fromBlocks A B Bᵀ C*Z = psdSchur p B C := by
    dsimp only [Z]
    rw [Matrix.transpose_fromRows, Matrix.transpose_neg, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    have hf : Hᵀ*p.leftInverse*A = Bᵀ := by
      rw [Matrix.mul_assoc, hVA]
      have hc := psd_offDiagonal_range p B C hD
      simpa only [H, Matrix.transpose_mul] using congrArg Matrix.transpose hc
    simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one, hf, neg_add_cancel,
      Matrix.zero_mul, zero_add]
    change -(Hᵀ*p.leftInverse*B)+C = C-Hᵀ*H
    dsimp only [H]
    simp only [Matrix.mul_assoc]
    module
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, heq] using hz

end
end HierarchicalAbsoluteSpectral
