import HierarchicalAbsoluteSpectral.MinMaxAffine
import HierarchicalAbsoluteSpectral.ThresholdInertiaBridge

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

theorem orderedEigenvalue_id_sub (A : Core k) (hA : A.IsHermitian) (j : Fin k) :
    orderedEigenvalue (1-A) (Matrix.isHermitian_one.sub hA) j =
      1-orderedEigenvalue A hA j.rev := by
  have hlin : (1-A).toEuclideanLin = LinearMap.id-A.toEuclideanLin := by
    simp only [map_sub,Matrix.toLpLin_one]
  let hS := LinearMap.IsSymmetric.id.sub (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
  have heig := ((Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_one.sub hA)).eigenvalues_eq_eigenvalues_iff
    finrank_euclideanSpace_fin hS finrank_euclideanSpace_fin).mpr (congrArg LinearMap.charpoly hlin)
  exact (congrFun heig j).trans (eigenvalues_id_sub A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace_fin j)

theorem orderedEigenvalue_neg (A : Core k) (hA : A.IsHermitian) (j : Fin k) :
    orderedEigenvalue (-A) hA.neg j = -orderedEigenvalue A hA j.rev := by
  have hs := orderedEigenvalue_shift (-A) hA.neg (-1) j
  have hi := orderedEigenvalue_id_sub A hA j
  have he : -A-(-1:ℝ) • (1 : Core k) = 1-A := by module
  have hh : orderedEigenvalue (-A) hA.neg j+1 = 1-orderedEigenvalue A hA j.rev := by
    calc
      _ = orderedEigenvalue (-A-(-1:ℝ) • (1 : Core k)) (shifted_isHermitian _ hA.neg (-1)) j := by
        simpa only [sub_neg_eq_add] using hs.symm
      _ = _ := by simpa only [he] using hi
  linarith

theorem negative_eigenvalue_congruence (A P : Core k) (hA : A.IsHermitian)
    (hP : IsUnit P.det) (j : Fin k) :
    orderedEigenvalue (Pᵀ*A*P) (normalized_isHermitian P A hA.eq) j < 0 ↔
      orderedEigenvalue A hA j < 0 := by
  have hh := positive_eigenvalue_congruence (-A) P hA.neg hP j.rev
  have hn : Pᵀ*(-A)*P = -(Pᵀ*A*P) := by simp only [Matrix.mul_neg,Matrix.neg_mul]
  have hleft : orderedEigenvalue (Pᵀ*(-A)*P) (normalized_isHermitian P (-A) hA.neg.eq) j.rev =
      -orderedEigenvalue (Pᵀ*A*P) (normalized_isHermitian P A hA.eq) j := by
    simpa only [hn,Fin.rev_rev] using orderedEigenvalue_neg (Pᵀ*A*P)
      (normalized_isHermitian P A hA.eq) j.rev
  rw [hleft,orderedEigenvalue_neg A hA j.rev,Fin.rev_rev] at hh
  simpa only [neg_pos] using hh

end
end HierarchicalAbsoluteSpectral
