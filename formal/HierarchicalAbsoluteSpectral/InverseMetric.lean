import HierarchicalAbsoluteSpectral.MatrixInequalities

/-!
The actual metric determined by an inverse factor. These identities are used
both to construct the refinement metric and to undo the strong-action norm.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

def inverseMetric (R : Core k) : Core k := (R⁻¹)ᵀ * R⁻¹

theorem inverseMetric_posDef (R : Core k) (hR : IsUnit R.det) :
    (inverseMetric R).PosDef := by
  apply Matrix.PosDef.conjTranspose_mul_self R⁻¹
    (Matrix.mulVec_injective_iff_isUnit.mpr ?_)
  exact (Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det R).mpr hR))

theorem inverseMetric_inv (R : Core k) (hR : IsUnit R.det) :
    (inverseMetric R)⁻¹ = R * Rᵀ := by
  letI := ((Matrix.isUnit_iff_isUnit_det R).mpr hR).invertible
  simp only [inverseMetric, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
    Matrix.inv_inv_of_invertible]

theorem inverseMetric_normalized (R : Core k) (hR : IsUnit R.det) :
    Rᵀ * inverseMetric R * R = 1 := by
  calc
    _ = (R⁻¹ * R)ᵀ * (R⁻¹ * R) := by
      simp only [inverseMetric, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul R hR]; simp

theorem inverseMetric_congruence (R A : Core k) (hR : IsUnit R.det) :
    (R⁻¹)ᵀ * (Rᵀ * A * R) * R⁻¹ = A := by
  calc
    _ = (R * R⁻¹)ᵀ * A * (R * R⁻¹) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [Matrix.mul_nonsing_inv R hR]; simp

theorem congruence_inverse (J A : Core k) :
    (Jᵀ * A * J)⁻¹ = J⁻¹ * A⁻¹ * (J⁻¹)ᵀ := by
  simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.transpose_nonsing_inv]

theorem congruence_defect (J A F : Core k) (hJ : IsUnit J.det) :
    Jᵀ * F * J - (Jᵀ * A * J) * (Jᵀ * F * J)⁻¹ * (Jᵀ * A * J) =
      Jᵀ * (F - A * F⁻¹ * A) * J := by
  have hproduct : (Jᵀ * A * J) * (Jᵀ * F * J)⁻¹ * (Jᵀ * A * J) =
      Jᵀ * (A * F⁻¹ * A) * J := by
    rw [congruence_inverse]
    calc
      _ = Jᵀ * A * (J * J⁻¹) * F⁻¹ * ((J * J⁻¹)ᵀ) * A * J := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Jᵀ * (A * F⁻¹ * A) * J := by
        rw [Matrix.mul_nonsing_inv J hJ]
        simp [Matrix.mul_assoc]
  rw [hproduct, Matrix.mul_sub, Matrix.sub_mul]

theorem inverseMetric_smul (R : Core k) (hR : IsUnit R.det) (c : ℝ) (hc : c ≠ 0) :
    inverseMetric (c • R) = (c⁻¹)^2 • inverseMetric R := by
  letI : Invertible c := invertibleOfNonzero hc
  simp [inverseMetric, Matrix.inv_smul _ _ hR, invOf_eq_inv,
    Matrix.transpose_smul, smul_smul, pow_two]

theorem inverseMetric_mul (R Q : Core k) :
    inverseMetric (R*Q) = (R⁻¹)ᵀ * inverseMetric Q * R⁻¹ := by
  simp [inverseMetric, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]

def inflatedInverseFactor (R : Core k) (ε : ℝ) : Core k :=
  (Real.sqrt (1+ε))⁻¹ • R

theorem inflatedInverseFactor_isUnit (R : Core k) (hR : IsUnit R.det)
    (ε : ℝ) (hε : 0 ≤ ε) : IsUnit (inflatedInverseFactor R ε).det := by
  rw [isUnit_iff_ne_zero, inflatedInverseFactor, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (by positivity)))
    (isUnit_iff_ne_zero.mp hR)

theorem inflatedInverseFactor_metric (R : Core k) (hR : IsUnit R.det)
    (ε : ℝ) (hε : 0 ≤ ε) :
    inverseMetric (inflatedInverseFactor R ε) = (1+ε) • inverseMetric R := by
  rw [inflatedInverseFactor, inverseMetric_smul R hR _ (inv_ne_zero (by positivity))]
  rw [inv_inv, Real.sq_sqrt (by linarith)]

end
end HierarchicalAbsoluteSpectral
