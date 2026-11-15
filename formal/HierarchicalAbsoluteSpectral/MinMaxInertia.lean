import HierarchicalAbsoluteSpectral.MinMaxAffine

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n k : ℕ}

theorem eigenvalue_pos_of_injective_form (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n)
    (V : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] E) (hV : Function.Injective V)
    (hform : ∀ z, z ≠ 0 → 0 < ⟪V z,T (V z)⟫_ℝ) :
    0 < hT.eigenvalues hn j := by
  let e := hT.eigenvectorBasis hn
  let f : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] (Fin j.val → ℝ) :=
    LinearMap.pi (fun i => (EuclideanSpace.proj ⟨i.val, lt_trans i.isLt j.isLt⟩).toLinearMap.comp
      (e.repr.toLinearEquiv.toLinearMap.comp V))
  have hdim : Module.finrank ℝ (Fin j.val → ℝ) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (j.val+1))) := by simp
  obtain ⟨z,hz,hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hhead : ∀ i : Fin n, i < j → e.repr (V z) i = 0 := by
    intro i hij
    have hh := congrFun (LinearMap.mem_ker.mp hz) ⟨i.val,hij⟩
    simpa only [f, LinearMap.pi_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, EuclideanSpace.coe_proj,
      Pi.zero_apply] using hh
  have htail := eigenbasis_tail_bound T hT hn j (V z) hhead
  have hpos := hform z hzne
  by_contra hh
  have hnonpos : hT.eigenvalues hn j ≤ 0 := le_of_not_gt hh
  have hm := mul_nonpos_of_nonpos_of_nonneg hnonpos (real_inner_self_nonneg (x := V z))
  linarith

theorem positive_eigenvalue_congruence_forward (A P : Core k) (hA : A.IsHermitian)
    (hP : IsUnit P.det) (j : Fin k) (hj : 0 < orderedEigenvalue A hA j) :
    0 < orderedEigenvalue (Pᵀ*A*P) (normalized_isHermitian P A hA.eq) j := by
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let V := spectralHeadEmbedding A.toEuclideanLin hs finrank_euclideanSpace_fin j
  let W := (P⁻¹).toEuclideanLin.comp V
  apply eigenvalue_pos_of_injective_form (Pᵀ*A*P).toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (normalized_isHermitian P A hA.eq))
    finrank_euclideanSpace_fin j W
    ((toEuclideanLin_injective_of_det _ (Matrix.isUnit_nonsing_inv_det P hP)).comp
      (spectralHeadEmbedding_injective _ hs finrank_euclideanSpace_fin j))
  intro z hz
  have hVz : V z ≠ 0 := by
    intro heq
    apply hz
    apply spectralHeadEmbedding_injective _ hs finrank_euclideanSpace_fin j
    simpa only [map_zero] using heq
  have hform := eigenbasis_head_bound A.toEuclideanLin hs finrank_euclideanSpace_fin j (V z)
    (fun i hi => spectralHeadEmbedding_tail_zero _ hs finrank_euclideanSpace_fin j z i hi)
  have hpositive : 0 < ⟪V z,A.toEuclideanLin (V z)⟫_ℝ :=
    (mul_pos hj (real_inner_self_pos.mpr hVz)).trans_le hform
  rw [← quadratic_eq_inner, quadratic_normalized, show P.toEuclideanLin (W z) = V z from
    toEuclideanLin_inv_cancel P hP _, quadratic_eq_inner]
  exact hpositive

/-- Sylvester sign invariance, for each exact sorted index. -/
theorem positive_eigenvalue_congruence (A P : Core k) (hA : A.IsHermitian)
    (hP : IsUnit P.det) (j : Fin k) :
    0 < orderedEigenvalue (Pᵀ*A*P) (normalized_isHermitian P A hA.eq) j ↔
      0 < orderedEigenvalue A hA j := by
  constructor
  · intro hj
    have hh := positive_eigenvalue_congruence_forward (Pᵀ*A*P) P⁻¹
      (normalized_isHermitian P A hA.eq) (Matrix.isUnit_nonsing_inv_det P hP) j hj
    simpa only [inverseMetric_congruence P A hP] using hh
  · exact positive_eigenvalue_congruence_forward A P hA hP j

theorem eigenvalues_add_smul_id (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (c : ℝ) (j : Fin n) :
    (hT.add (LinearMap.IsSymmetric.id.smul (by simp : star c = c))).eigenvalues hn j =
      hT.eigenvalues hn j+c := by
  let S := T+c • LinearMap.id
  let hS := hT.add (LinearMap.IsSymmetric.id.smul (by simp : star c = c))
  apply le_antisymm
  · apply eigenvalue_upper_of_tail_form S T hS hT hn j
    intro v hv
    have hh := eigenbasis_tail_bound T hT hn j v hv
    change ⟪v,(T+c • LinearMap.id : E →ₗ[ℝ] E) v⟫_ℝ ≤ _
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_add_right, inner_smul_right]
    nlinarith
  · apply eigenvalue_lower_of_injective_form S hS hn j (spectralHeadEmbedding T hT hn j)
      (spectralHeadEmbedding_injective T hT hn j)
    intro z
    have hh := eigenbasis_head_bound T hT hn j (spectralHeadEmbedding T hT hn j z)
      (fun i hi => spectralHeadEmbedding_tail_zero T hT hn j z i hi)
    change _ ≤ ⟪_,(T+c • LinearMap.id : E →ₗ[ℝ] E) _⟫_ℝ
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_add_right, inner_smul_right]
    nlinarith

end
end HierarchicalAbsoluteSpectral
