import HierarchicalAbsoluteSpectral.MinMaxEigen
import HierarchicalAbsoluteSpectral.InverseMetric
import HierarchicalAbsoluteSpectral.IdealMetric

/-!
Sorted generalized eigenvalues and their comparison under changes of mass.
The factors in this file are analytical changes of coordinates. They do not
provide the algorithm with eigenvalue or square-root primitives.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k : ℕ}

def orderedEigenvalue (A : Core k) (hA : A.IsHermitian) (j : Fin k) : ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin j

theorem quadratic_eq_inner (A : Core k) (v : EuclideanSpace ℝ (Fin k)) :
    quadratic A (ofLp v) = ⟪v,A.toEuclideanLin v⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
    star_trivial, quadratic]
  exact dotProduct_comm _ _

theorem orderedEigenvalue_mono (A B : Core k) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) (j : Fin k) :
    orderedEigenvalue A hA j ≤ orderedEigenvalue B hB j := by
  apply eigenvalues_mono_of_inner A.toEuclideanLin B.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace_fin
  intro v
  simpa only [← quadratic_eq_inner] using quadratic_mono hAB (ofLp v)

theorem orderedEigenvalue_nonneg (A : Core k) (hA : A.PosSemidef) (j : Fin k) :
    0 ≤ orderedEigenvalue A hA.isHermitian j := by
  have hp : A.toEuclideanLin.IsPositive :=
    ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian, fun v => by
      rw [real_inner_comm, ← quadratic_eq_inner]
      exact quadratic_nonneg hA _⟩
  exact hp.nonneg_eigenvalues finrank_euclideanSpace_fin j

theorem toEuclideanLin_injective_of_det (R : Core k) (hR : IsUnit R.det) :
    Function.Injective R.toEuclideanLin := by
  intro v w hvw
  apply ofLp_injective
  apply Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det R).mpr hR)
  simpa only [Matrix.toEuclideanLin_apply, ofLp_toLp] using congrArg ofLp hvw

theorem quadratic_normalized (A R : Core k) (v : EuclideanSpace ℝ (Fin k)) :
    quadratic (Rᵀ*A*R) (ofLp v) = quadratic A (ofLp (R.toEuclideanLin v)) := by
  simpa only [Matrix.toEuclideanLin_apply, ofLp_toLp, Matrix.transpose_transpose]
    using quadratic_congruence A Rᵀ (ofLp v)

theorem metric_norm_identity (R : Core k) (hR : IsUnit R.det)
    (v : EuclideanSpace ℝ (Fin k)) :
    quadratic (inverseMetric R) (ofLp (R.toEuclideanLin v)) = ⟪v,v⟫_ℝ := by
  rw [← quadratic_normalized, inverseMetric_normalized R hR, quadratic_eq_inner]
  simp

theorem toEuclideanLin_inv_cancel (R : Core k) (hR : IsUnit R.det)
    (v : EuclideanSpace ℝ (Fin k)) :
    R.toEuclideanLin ((R⁻¹).toEuclideanLin v) = v := by
  simp only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv R hR, Matrix.one_mulVec, toLp_ofLp]

/-- Increasing a positive mass by at most a factor `a` decreases each
generalized eigenvalue by at most that factor. The two factors may differ
and need not commute with `Q` or with one another. -/
theorem generalizedEigenvalue_lower (Q R₁ R₂ : Core k) (hQ : Q.PosSemidef)
    (hR₁ : IsUnit R₁.det) (hR₂ : IsUnit R₂.det) (a : ℝ) (ha : 0 < a)
    (hmass : inverseMetric R₂ ≤ a • inverseMetric R₁) (j : Fin k) :
    orderedEigenvalue (R₁ᵀ*Q*R₁) (normalized_isHermitian R₁ Q hQ.isHermitian.eq) j / a ≤
      orderedEigenvalue (R₂ᵀ*Q*R₂) (normalized_isHermitian R₂ Q hQ.isHermitian.eq) j := by
  let A₁ := R₁ᵀ*Q*R₁
  let A₂ := R₂ᵀ*Q*R₂
  have hA₁ := normalized_isHermitian R₁ Q hQ.isHermitian.eq
  have hA₂ := normalized_isHermitian R₂ Q hQ.isHermitian.eq
  let S₁ := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA₁
  let S₂ := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA₂
  let V := spectralHeadEmbedding A₁.toEuclideanLin S₁ finrank_euclideanSpace_fin j
  let W := (R₂⁻¹).toEuclideanLin.comp (R₁.toEuclideanLin.comp V)
  have hW : Function.Injective W :=
    (toEuclideanLin_injective_of_det _ (Matrix.isUnit_nonsing_inv_det R₂ hR₂)).comp
      ((toEuclideanLin_injective_of_det R₁ hR₁).comp
        (spectralHeadEmbedding_injective _ S₁ finrank_euclideanSpace_fin j))
  have hpos : 0 ≤ orderedEigenvalue A₁ hA₁ j :=
    orderedEigenvalue_nonneg _ (hQ.conjTranspose_mul_mul_same R₁) j
  apply eigenvalue_lower_of_injective_form A₂.toEuclideanLin S₂
    finrank_euclideanSpace_fin j W hW
  intro z
  have hchange : R₂.toEuclideanLin (W z) = R₁.toEuclideanLin (V z) :=
    toEuclideanLin_inv_cancel R₂ hR₂ _
  have hnorm : ⟪W z,W z⟫_ℝ ≤ a*⟪V z,V z⟫_ℝ := by
    have hh := quadratic_mono hmass (ofLp (R₁.toEuclideanLin (V z)))
    rw [quadratic_smul, metric_norm_identity R₁ hR₁, ← hchange,
      metric_norm_identity R₂ hR₂] at hh
    exact hh
  have hhead : orderedEigenvalue A₁ hA₁ j*⟪V z,V z⟫_ℝ ≤
      ⟪V z,A₁.toEuclideanLin (V z)⟫_ℝ := by
    apply eigenbasis_head_bound A₁.toEuclideanLin S₁ finrank_euclideanSpace_fin j
    exact fun i hi => spectralHeadEmbedding_tail_zero _ S₁ finrank_euclideanSpace_fin j z i hi
  calc
    _ ≤ (orderedEigenvalue A₁ hA₁ j/a)*(a*⟪V z,V z⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hnorm (div_nonneg hpos ha.le)
    _ = orderedEigenvalue A₁ hA₁ j*⟪V z,V z⟫_ℝ := by field_simp
    _ ≤ ⟪V z,A₁.toEuclideanLin (V z)⟫_ℝ := hhead
    _ = ⟪W z,A₂.toEuclideanLin (W z)⟫_ℝ := by
      rw [← quadratic_eq_inner, ← quadratic_eq_inner,
        quadratic_normalized, quadratic_normalized, hchange]

/-- The two-sided mass comparison (equation (4)), with zero-based sorted
eigenvalue indices and no restriction on repeated or zero eigenvalues. -/
theorem generalizedEigenvalue_mass_compare (Q R₁ R₂ : Core k) (hQ : Q.PosSemidef)
    (hR₁ : IsUnit R₁.det) (hR₂ : IsUnit R₂.det) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε < 1)
    (hlo : (1-ε) • inverseMetric R₁ ≤ inverseMetric R₂)
    (hhi : inverseMetric R₂ ≤ (1+ε) • inverseMetric R₁) (j : Fin k) :
    orderedEigenvalue (R₁ᵀ*Q*R₁) (normalized_isHermitian R₁ Q hQ.isHermitian.eq) j/(1+ε) ≤
      orderedEigenvalue (R₂ᵀ*Q*R₂) (normalized_isHermitian R₂ Q hQ.isHermitian.eq) j ∧
    orderedEigenvalue (R₂ᵀ*Q*R₂) (normalized_isHermitian R₂ Q hQ.isHermitian.eq) j ≤
      orderedEigenvalue (R₁ᵀ*Q*R₁) (normalized_isHermitian R₁ Q hQ.isHermitian.eq) j/(1-ε) := by
  constructor
  · exact generalizedEigenvalue_lower Q R₁ R₂ hQ hR₁ hR₂ (1+ε) (by linarith) hhi j
  · have hp : 0 < 1-ε := by linarith
    have hrev : inverseMetric R₁ ≤ (1-ε)⁻¹ • inverseMetric R₂ := by
      have hh := smul_le_smul_of_nonneg_left hlo (inv_nonneg.mpr hp.le)
      simpa only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul] using hh
    have hh := generalizedEigenvalue_lower Q R₂ R₁ hQ hR₂ hR₁
      (1-ε)⁻¹ (inv_pos.mpr hp) hrev j
    rw [div_inv_eq_mul] at hh
    exact (le_div_iff₀ hp).mpr hh

end
end HierarchicalAbsoluteSpectral
