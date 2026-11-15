import HierarchicalAbsoluteSpectral.MatrixInequalities
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Block Cholesky with an inverse factor, using only multiplication,
subtraction, field inverses and one-dimensional square roots at leaves. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

structure FiniteGramPair (D : Matrix n n ℝ) where
  upper : Matrix n n ℝ
  inverse : Matrix n n ℝ
  gram : upperᵀ*upper = D
  left_inverse : inverse*upper = 1
  right_inverse : upper*inverse = 1

namespace FiniteGramPair

theorem isUnit {D : Matrix n n ℝ} (p : FiniteGramPair D) : IsUnit p.upper :=
  ⟨⟨p.upper, p.inverse, p.right_inverse, p.left_inverse⟩, rfl⟩

theorem inverse_eq {D : Matrix n n ℝ} (p : FiniteGramPair D) :
    p.inverse = p.upper⁻¹ := (Matrix.inv_eq_left_inv p.left_inverse).symm

end FiniteGramPair

def choleskyOffDiagonal {A : Matrix m m ℝ} (p : FiniteGramPair A)
    (B : Matrix m n ℝ) : Matrix m n ℝ := p.inverseᵀ*B

def choleskySchur {A : Matrix m m ℝ} (p : FiniteGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ) : Matrix n n ℝ :=
  C-(choleskyOffDiagonal p B)ᵀ*choleskyOffDiagonal p B

theorem choleskySchur_posDef {A : Matrix m m ℝ} (p : FiniteGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosDef) : (choleskySchur p B C).PosDef := by
  let H := choleskyOffDiagonal p B
  let Z : Matrix (m ⊕ n) n ℝ := Matrix.fromRows (-(p.inverse*H)) 1
  have hZ : Function.Injective Z.mulVec := by
    intro x y hxy
    have hb := congrArg (fun v => v ∘ Sum.inr) hxy
    simpa only [Z, Matrix.fromRows_mulVec, Matrix.one_mulVec, Sum.elim_comp_inr] using hb
  have hz := hD.conjTranspose_mul_mul_same hZ
  have heq : Zᵀ * Matrix.fromBlocks A B Bᵀ C * Z = choleskySchur p B C := by
    have hUH : p.upperᵀ*H = B := by
      dsimp [H, choleskyOffDiagonal]
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, p.left_inverse]
      simp
    have hHV : Hᵀ*p.upper = Bᵀ := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hUH
    dsimp only [Z]
    rw [Matrix.transpose_fromRows, Matrix.transpose_neg, Matrix.transpose_mul,
      Matrix.transpose_one, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    have hVA : p.inverseᵀ*A = p.upper := by
      calc
        _ = p.inverseᵀ*(p.upperᵀ*p.upper) := congrArg (p.inverseᵀ*·) p.gram.symm
        _ = (p.upper*p.inverse)ᵀ*p.upper := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = p.upper := by rw [p.right_inverse]; simp
    have hf : Hᵀ*p.inverseᵀ*A = Bᵀ := by rw [Matrix.mul_assoc, hVA, hHV]
    simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one, hf, neg_add_cancel,
      Matrix.zero_mul, zero_add]
    change -(Hᵀ*p.inverseᵀ*B)+C = C-Hᵀ*H
    change -(Hᵀ*p.inverseᵀ*B)+C = C-Hᵀ*(p.inverseᵀ*B)
    simp only [Matrix.mul_assoc]; module
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, heq] using hz

def choleskyBlockPair {A : Matrix m m ℝ} (p : FiniteGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (q : FiniteGramPair (choleskySchur p B C)) :
    FiniteGramPair (Matrix.fromBlocks A B Bᵀ C) where
  upper := Matrix.fromBlocks p.upper (choleskyOffDiagonal p B) 0 q.upper
  inverse := Matrix.fromBlocks p.inverse (-(p.inverse*choleskyOffDiagonal p B*q.inverse)) 0 q.inverse
  gram := by
    have hUH : p.upperᵀ*choleskyOffDiagonal p B = B := by
      rw [choleskyOffDiagonal, ← Matrix.mul_assoc, ← Matrix.transpose_mul, p.left_inverse]
      simp
    have hHU : (choleskyOffDiagonal p B)ᵀ*p.upper = Bᵀ := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hUH
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      p.gram, hUH, hHU, q.gram, choleskySchur, add_sub_cancel]
  left_inverse := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      p.left_inverse, q.left_inverse, Matrix.neg_mul, Matrix.mul_assoc]
    simp only [Matrix.mul_one, add_neg_cancel, Matrix.fromBlocks_one]
  right_inverse := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
      p.right_inverse, q.right_inverse, Matrix.mul_neg]
    simp only [← Matrix.mul_assoc, p.right_inverse, Matrix.one_mul, neg_add_cancel,
      neg_zero, zero_add, Matrix.fromBlocks_one]

end
end HierarchicalAbsoluteSpectral
