import HierarchicalAbsoluteSpectral.MinMaxInertia
import HierarchicalAbsoluteSpectral.ThresholdKrylovGraph

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

theorem matrix_rayleigh_abs_le (A : Core k) (v : EuclideanSpace ℝ (Fin k)) :
    |⟪v,A.toEuclideanLin v⟫_ℝ| ≤ ‖A‖*⟪v,v⟫_ℝ := by
  calc
    _ ≤ ‖v‖*‖A.toEuclideanLin v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖A‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (matrix_toEuclideanLin_norm_le A v) (norm_nonneg _)
    _ = _ := by rw [real_inner_self_eq_norm_sq]; ring

theorem orderedEigenvalue_le_add_norm (A B : Core k) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (j : Fin k) :
    orderedEigenvalue A hA j ≤ orderedEigenvalue B hB j+‖A-B‖ := by
  apply eigenvalue_upper_of_tail_form A.toEuclideanLin B.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace_fin j
  intro v hv
  have htail := eigenbasis_tail_bound B.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace_fin j v hv
  have hnorm := (le_abs_self ⟪v,(A-B).toEuclideanLin v⟫_ℝ).trans (matrix_rayleigh_abs_le (A-B) v)
  simp only [map_sub, LinearMap.sub_apply, inner_sub_right] at hnorm
  dsimp only [orderedEigenvalue]
  nlinarith only [htail,hnorm]

/-- Sorted Hermitian eigenvalues are 1-Lipschitz in the actual L2 operator
norm. This gives the measurable spectral predicates needed when threshold
operators depend on earlier random queries. -/
theorem orderedEigenvalue_abs_sub_le (A B : Core k) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (j : Fin k) :
    |orderedEigenvalue A hA j-orderedEigenvalue B hB j| ≤ ‖A-B‖ := by
  have h₁ := orderedEigenvalue_le_add_norm A B hA hB j
  have h₂ := orderedEigenvalue_le_add_norm B A hB hA j
  rw [norm_sub_rev] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem orderedEigenvalue_lipschitz (j : Fin k) :
    LipschitzWith 1 (fun A : {A : Core k // A.IsHermitian} => orderedEigenvalue A.val A.property j) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    orderedEigenvalue_abs_sub_le A.val B.val A.property B.property j

theorem orderedEigenvalue_continuous (j : Fin k) :
    Continuous (fun A : {A : Core k // A.IsHermitian} => orderedEigenvalue A.val A.property j) :=
  (orderedEigenvalue_lipschitz j).continuous

theorem orderedEigenvalue_measurable (j : Fin k)
    [MeasurableSpace {A : Core k // A.IsHermitian}]
    [BorelSpace {A : Core k // A.IsHermitian}] :
    Measurable (fun A : {A : Core k // A.IsHermitian} => orderedEigenvalue A.val A.property j) :=
  (orderedEigenvalue_continuous j).measurable

end
end HierarchicalAbsoluteSpectral
