import HierarchicalAbsoluteSpectral.MassSpectrumSingular

/-! Sorted Ritz values of actual orthonormal compressions. These are proof
objects; the query program will test their signs by exact shifted inertia. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {k w j : ℕ}

theorem quadratic_compression (A : Core k) (U : Matrix (Fin k) (Fin w) ℝ)
    (v : EuclideanSpace ℝ (Fin w)) :
    quadratic (Uᵀ*A*U) (ofLp v) = quadratic A (ofLp (U.toEuclideanLin v)) := by
  simpa only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.transpose_transpose]
    using quadratic_congruence A Uᵀ (ofLp v)

theorem orthonormal_toEuclideanLin_inner (U : Matrix (Fin k) (Fin w) ℝ)
    (hU : Uᵀ*U = 1) (v : EuclideanSpace ℝ (Fin w)) :
    ⟪U.toEuclideanLin v,U.toEuclideanLin v⟫_ℝ = ⟪v,v⟫_ℝ := by
  have hh := quadratic_compression (1 : Core k) U v
  simpa only [Matrix.mul_one, hU, quadratic_eq_inner, Matrix.toLpLin_one,
    LinearMap.one_apply] using hh.symm

theorem orthonormal_toEuclideanLin_injective (U : Matrix (Fin k) (Fin w) ℝ)
    (hU : Uᵀ*U = 1) : Function.Injective U.toEuclideanLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← orthonormal_toEuclideanLin_inner U hU z, hz]
  simp

theorem compression_isHermitian (A : Core k) (hA : A.IsHermitian)
    (U : Matrix (Fin k) (Fin w) ℝ) : (Uᵀ*A*U).IsHermitian := by
  have hAT : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, hAT, Matrix.mul_assoc]

/-- Every compressed Ritz value is bounded by the corresponding eigenvalue
of the full operator, on every run of the algorithm. -/
theorem orderedEigenvalue_compression_le (A : Core k) (hA : A.IsHermitian)
    (U : Matrix (Fin k) (Fin w) ℝ) (hU : Uᵀ*U = 1)
    (j : ℕ) (hjw : j < w) (hjk : j < k) :
    orderedEigenvalue (Uᵀ*A*U) (compression_isHermitian A hA U) ⟨j,hjw⟩ ≤
      orderedEigenvalue A hA ⟨j,hjk⟩ := by
  let B := Uᵀ*A*U
  let hB := Matrix.isSymmetric_toEuclideanLin_iff.mpr (compression_isHermitian A hA U)
  let V := spectralHeadEmbedding B.toEuclideanLin hB finrank_euclideanSpace_fin ⟨j,hjw⟩
  apply eigenvalue_lower_of_injective_form A.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace_fin ⟨j,hjk⟩
    (U.toEuclideanLin.comp V)
    ((orthonormal_toEuclideanLin_injective U hU).comp
      (spectralHeadEmbedding_injective _ hB finrank_euclideanSpace_fin ⟨j,hjw⟩))
  intro z
  have hh := eigenbasis_head_bound B.toEuclideanLin hB finrank_euclideanSpace_fin ⟨j,hjw⟩ (V z)
    (fun i hi => spectralHeadEmbedding_tail_zero _ hB finrank_euclideanSpace_fin ⟨j,hjw⟩ z i hi)
  simpa only [orderedEigenvalue, LinearMap.comp_apply, orthonormal_toEuclideanLin_inner U hU,
    ← quadratic_eq_inner, B, quadratic_compression] using hh

/-- A constructed dimension-(j+1) polynomial graph in the computed span
forces the j-th compressed Ritz value above its Rayleigh lower bound. -/
theorem orderedEigenvalue_compression_lower (A : Core k) (hA : A.IsHermitian)
    (U : Matrix (Fin k) (Fin w) ℝ) (hU : Uᵀ*U = 1)
    (Y : Matrix (Fin k) (Fin (j+1)) ℝ) (X : Matrix (Fin w) (Fin (j+1)) ℝ)
    (hY : Function.Injective Y.toEuclideanLin) (hspan : Y = U*X)
    (a : ℝ) (hform : ∀ z, a*⟪Y.toEuclideanLin z,Y.toEuclideanLin z⟫_ℝ ≤
      ⟪Y.toEuclideanLin z,A.toEuclideanLin (Y.toEuclideanLin z)⟫_ℝ)
    (hjw : j < w) :
    a ≤ orderedEigenvalue (Uᵀ*A*U) (compression_isHermitian A hA U) ⟨j,hjw⟩ := by
  have hlin : Y.toEuclideanLin = U.toEuclideanLin.comp X.toEuclideanLin := by
    rw [hspan, Matrix.toLpLin_mul]
  have hX : Function.Injective X.toEuclideanLin := by
    intro z z' hz
    apply hY
    simp only [hlin, LinearMap.comp_apply, hz]
  apply eigenvalue_lower_of_injective_form (Uᵀ*A*U).toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (compression_isHermitian A hA U))
    finrank_euclideanSpace_fin ⟨j,hjw⟩ X.toEuclideanLin hX a
  intro z
  have hh := hform z
  simpa only [hlin, LinearMap.comp_apply, orthonormal_toEuclideanLin_inner U hU,
    ← quadratic_eq_inner, ← quadratic_compression] using hh

end
end HierarchicalAbsoluteSpectral
