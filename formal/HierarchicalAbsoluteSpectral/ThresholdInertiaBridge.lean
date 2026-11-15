import HierarchicalAbsoluteSpectral.MinMaxDiagonalCount
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertia

set_option backward.isDefEq.respectTransparency false

/-! Exact pivot counts are connected to the same sorted eigenvalues used in
the Krylov theorem. No numerical extraction or root isolation is involved. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

theorem FiniteCongruenceDiagonal.eigenvalue_pos_iff {A : Core k}
    (out : FiniteCongruenceDiagonal A) (hA : A.IsHermitian) (j : Fin k) :
    0 < orderedEigenvalue A hA j ↔ j.val < out.positiveCount := by
  have hc := positive_eigenvalue_congruence A out.basis hA out.isUnit_det j
  have hd : 0 < orderedEigenvalue (out.basisᵀ*A*out.basis)
      (normalized_isHermitian out.basis A hA.eq) j ↔ j.val < out.positiveCount := by
    simpa only [out.congruence, FiniteCongruenceDiagonal.positiveCount, diagonalPositiveCount] using
      diagonal_eigenvalue_pos_iff out.diagonal j
  exact hc.symm.trans hd

theorem shifted_isHermitian (A : Core k) (hA : A.IsHermitian) (c : ℝ) :
    (A-c • (1 : Core k)).IsHermitian := by
  have hAT : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hAT]

theorem orderedEigenvalue_shift (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    orderedEigenvalue (A-c • (1 : Core k)) (shifted_isHermitian A hA c) j =
      orderedEigenvalue A hA j-c := by
  have hlin : (A-c • (1 : Core k)).toEuclideanLin =
      A.toEuclideanLin+(-c) • LinearMap.id := by
    simp only [map_sub, map_smul, Matrix.toLpLin_one]
    module
  have hh := eigenvalues_add_smul_id A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace_fin (-c) j
  have heig := ((Matrix.isSymmetric_toEuclideanLin_iff.mpr (shifted_isHermitian A hA c)).eigenvalues_eq_eigenvalues_iff finrank_euclideanSpace_fin
      ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).add
        (LinearMap.IsSymmetric.id.smul (by simp : star (-c) = -c)))
      finrank_euclideanSpace_fin).mpr (congrArg LinearMap.charpoly hlin)
  exact (congrFun heig j).trans hh

theorem FiniteCongruenceDiagonal.shifted_eigenvalue_gt_iff (A : Core k)
    (hA : A.IsHermitian) (c : ℝ) (out : FiniteCongruenceDiagonal (A-c • (1 : Core k)))
    (j : Fin k) : c < orderedEigenvalue A hA j ↔ j.val < out.positiveCount := by
  have hh := out.eigenvalue_pos_iff (shifted_isHermitian A hA c) j
  rw [orderedEigenvalue_shift A hA c j] at hh
  simpa only [sub_pos] using hh

end
end HierarchicalAbsoluteSpectral
