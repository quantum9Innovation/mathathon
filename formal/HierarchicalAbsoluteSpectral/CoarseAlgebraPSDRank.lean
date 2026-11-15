import HierarchicalAbsoluteSpectral.CoarseAlgebraRange

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem PSDGramPair.dimension_eq_rank {D : Matrix n n ℝ} (p : PSDGramPair D) :
    p.dimension = D.rank := by
  have hr : p.factor.rank = p.dimension := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using Matrix.rank_le_card_width p.factor
    · calc
        _ = (1 : Matrix (Fin p.dimension) (Fin p.dimension) ℝ).rank := by simp [Matrix.rank_one]
        _ = (p.leftInverse*p.factor).rank := congrArg Matrix.rank p.left_inverse.symm
        _ ≤ p.factor.rank := Matrix.rank_mul_le_right _ _
  calc
    _ = p.factor.rank := hr.symm
    _ = (p.factor*p.factorᵀ).rank := (Matrix.rank_self_mul_transpose p.factor).symm
    _ = D.rank := congrArg Matrix.rank p.gram

theorem psdSchur_rank_le {A : Matrix m m ℝ} (p : PSDGramPair A)
    (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef) :
    (psdSchur p B C).rank ≤ (Matrix.fromBlocks A B Bᵀ C).rank := by
  let H := p.leftInverse*B
  let Z : Matrix (m ⊕ n) n ℝ := Matrix.fromRows (-(p.leftInverseᵀ*H)) 1
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
  rw [← heq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end
end HierarchicalAbsoluteSpectral
