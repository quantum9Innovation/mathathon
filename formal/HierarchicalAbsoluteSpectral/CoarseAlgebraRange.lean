import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDBlock
import Mathlib.LinearAlgebra.Matrix.Rank

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {m w : ℕ}

structure OrthogonalRange (Y : Matrix (Fin m) (Fin w) ℝ) where
  dimension : ℕ
  dimension_le_rows : dimension ≤ m
  dimension_le_cols : dimension ≤ w
  basis : Matrix (Fin m) (Fin dimension) ℝ
  coefficients : Matrix (Fin dimension) (Fin w) ℝ
  orthogonal : basisᵀ*basis = 1
  spans : Y = basis*coefficients
  dimension_eq_rank : dimension = Y.rank

def rangeFromPSDGram (Y : Matrix (Fin m) (Fin w) ℝ)
    (p : PSDGramPair (Yᵀ*Y)) : OrthogonalRange Y := by
  let Q := Y*p.leftInverseᵀ
  have horth : Qᵀ*Q = 1 := by
    calc
      _ = p.leftInverse*(Yᵀ*Y)*p.leftInverseᵀ := by
        simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = p.leftInverse*(p.factor*p.factorᵀ)*p.leftInverseᵀ :=
        congrArg (fun A => p.leftInverse*A*p.leftInverseᵀ) p.gram.symm
      _ = (p.leftInverse*p.factor)*(p.leftInverse*p.factor)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [p.left_inverse]; simp
  have hQY : Qᵀ*Y = p.factorᵀ := by
    calc
      _ = p.leftInverse*(Yᵀ*Y) := by
        simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = p.leftInverse*(p.factor*p.factorᵀ) := congrArg (p.leftInverse*·) p.gram.symm
      _ = p.factorᵀ := by rw [← Matrix.mul_assoc, p.left_inverse]; simp
  have hYQ : Yᵀ*Q = p.factor := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hQY
  have hsq : (Y-Q*p.factorᵀ)ᵀ*(Y-Q*p.factorᵀ) = 0 := by
    calc
      _ = Yᵀ*Y-(Yᵀ*Q)*p.factorᵀ-p.factor*(Qᵀ*Y)+p.factor*(Qᵀ*Q)*p.factorᵀ := by
        simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
        module
      _ = 0 := by rw [hYQ, hQY, horth, Matrix.mul_one, p.gram]; module
  have hzero : Y-Q*p.factorᵀ = 0 := by
    apply (Matrix.conjTranspose_mul_self_eq_zero).mp
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsq
  have hspan : Y = Q*p.factorᵀ := sub_eq_zero.mp hzero
  have hdim : Q.rank = p.dimension := by
    rw [← Matrix.rank_transpose_mul_self Q, horth, Matrix.rank_one, Fintype.card_fin]
  have hrank : Y.rank = p.dimension := by
    apply le_antisymm
    · calc
        _ = (Q*p.factorᵀ).rank := congrArg Matrix.rank hspan
        _ ≤ Q.rank := Matrix.rank_mul_le_left _ _
        _ = p.dimension := hdim
    · rw [← hdim]
      exact Matrix.rank_mul_le_left Y p.leftInverseᵀ
  refine ⟨p.dimension, ?_, ?_, Q, p.factorᵀ, horth, hspan, hrank.symm⟩
  · rw [← hdim]
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_height Q
  · simpa only [Fintype.card_fin] using p.dimension_le

end
end HierarchicalAbsoluteSpectral
