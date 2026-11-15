import HierarchicalAbsoluteSpectral.MinMaxNegation

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

theorem orderedEigenvalue_smul_nonneg (A : Core k) (hA : A.IsHermitian)
    (c : ℝ) (hc : 0≤c) (j : Fin k) :
    orderedEigenvalue (c • A) (hA.smul (by simp : star c=c)) j =
      c*orderedEigenvalue A hA j := by
  let T := A.toEuclideanLin
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let S := (c • A).toEuclideanLin
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.smul (by simp : star c=c))
  apply le_antisymm
  · apply eigenvalue_upper_of_tail_form S T hS hT finrank_euclideanSpace_fin j
    intro v hv
    have hh := mul_le_mul_of_nonneg_left (eigenbasis_tail_bound T hT finrank_euclideanSpace_fin j v hv) hc
    change ⟪v,(c • A).toEuclideanLin v⟫_ℝ ≤ _
    simp only [map_smul,LinearMap.smul_apply,inner_smul_right]
    dsimp only [T,hT,orderedEigenvalue] at hh ⊢
    nlinarith only [hh]
  · apply eigenvalue_lower_of_injective_form S hS finrank_euclideanSpace_fin j
      (spectralHeadEmbedding T hT finrank_euclideanSpace_fin j)
      (spectralHeadEmbedding_injective T hT finrank_euclideanSpace_fin j)
    intro z
    have hh := mul_le_mul_of_nonneg_left (eigenbasis_head_bound T hT finrank_euclideanSpace_fin j
      (spectralHeadEmbedding T hT finrank_euclideanSpace_fin j z)
      (fun i hi => spectralHeadEmbedding_tail_zero T hT finrank_euclideanSpace_fin j z i hi)) hc
    change _ ≤ ⟪_,(c • A).toEuclideanLin _⟫_ℝ
    simp only [map_smul,LinearMap.smul_apply,inner_smul_right]
    dsimp only [T,hT,orderedEigenvalue] at hh ⊢
    nlinarith only [hh]

end
end HierarchicalAbsoluteSpectral
