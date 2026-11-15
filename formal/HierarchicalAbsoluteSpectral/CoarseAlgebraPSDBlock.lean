import HierarchicalAbsoluteSpectral.CoarseAlgebraPSD

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def psdBlockPairOfEq {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    {S : Matrix n n ℝ} (q : PSDGramPair S) (hS : S = psdSchur p B C) :
    PSDGramPair (Matrix.fromBlocks A B Bᵀ C) := by
  let H := p.leftInverse*B
  let L : Matrix (m ⊕ n) (Fin p.dimension ⊕ Fin q.dimension) ℝ :=
    Matrix.fromBlocks p.factor 0 Hᵀ q.factor
  let U : Matrix (Fin p.dimension ⊕ Fin q.dimension) (m ⊕ n) ℝ :=
    Matrix.fromBlocks p.leftInverse 0 (-(q.leftInverse*Hᵀ*p.leftInverse)) q.leftInverse
  have hLH : p.factor*H = B := psd_offDiagonal_range p B C hD
  have hHL : Hᵀ*p.factorᵀ = Bᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hLH
  have hGram : L*Lᵀ = Matrix.fromBlocks A B Bᵀ C := by
    dsimp only [L]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.transpose_transpose, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, p.gram, q.gram, hS, hLH, hHL, psdSchur, H,
      add_sub_cancel]
  have hLeft : U*L = 1 := by
    dsimp only [U, L]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      p.left_inverse, q.left_inverse, Matrix.neg_mul]
    have he : q.leftInverse*Hᵀ*p.leftInverse*p.factor = q.leftInverse*Hᵀ := by
      calc
        _ = q.leftInverse*Hᵀ*(p.leftInverse*p.factor) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [p.left_inverse, Matrix.mul_one]
    rw [he]
    simp
  let e : Fin (p.dimension+q.dimension) ≃ Fin p.dimension ⊕ Fin q.dimension := finSumFinEquiv.symm
  refine ⟨p.dimension+q.dimension, ?_, L.submatrix id e, U.submatrix e id, ?_, ?_⟩
  · simpa only [Fintype.card_sum] using Nat.add_le_add p.dimension_le q.dimension_le
  · change L.submatrix id e*Lᵀ.submatrix e id = _
    rw [Matrix.submatrix_mul_equiv, hGram]
    rfl
  · change U.submatrix e (Equiv.refl _)*L.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv, hLeft, Matrix.submatrix_one_equiv]

def psdBlockPair {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (q : PSDGramPair (psdSchur p B C)) : PSDGramPair (Matrix.fromBlocks A B Bᵀ C) :=
  psdBlockPairOfEq p B C hD q rfl

namespace PSDGramPair

def cast {n : Type} [Fintype n] [DecidableEq n] {D E : Matrix n n ℝ}
    (p : PSDGramPair D) (h : D = E) : PSDGramPair E := h ▸ p

def reindex {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {D : Matrix n n ℝ} (p : PSDGramPair D) (e : m ≃ n) : PSDGramPair (D.submatrix e e) where
  dimension := p.dimension
  dimension_le := by simpa only [Fintype.card_congr e] using p.dimension_le
  factor := p.factor.submatrix e id
  leftInverse := p.leftInverse.submatrix id e
  gram := by
    change p.factor.submatrix e (Equiv.refl _)*p.factorᵀ.submatrix (Equiv.refl _) e = _
    rw [Matrix.submatrix_mul_equiv, p.gram]
  left_inverse := by
    rw [Matrix.submatrix_mul_equiv, p.left_inverse]
    rfl

end PSDGramPair

end
end HierarchicalAbsoluteSpectral
