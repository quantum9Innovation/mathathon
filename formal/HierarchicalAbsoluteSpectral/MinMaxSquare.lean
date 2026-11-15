import HierarchicalAbsoluteSpectral.MinMaxNear

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open WithLp Matrix
open scoped InnerProductSpace MatrixOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n k : ℕ}

theorem eigenvalue_upper_of_tail_form (S T : E →ₗ[ℝ] E) (hS : S.IsSymmetric)
    (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) (j : Fin n) (c : ℝ)
    (htail : ∀ v, (∀ i : Fin n, i < j → (hT.eigenvectorBasis hn).repr v i = 0) →
      ⟪v,S v⟫_ℝ ≤ c*⟪v,v⟫_ℝ) :
    hS.eigenvalues hn j ≤ c := by
  let V := spectralHeadEmbedding S hS hn j
  let e := hT.eigenvectorBasis hn
  let f : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] (Fin j.val → ℝ) :=
    LinearMap.pi (fun i => (EuclideanSpace.proj ⟨i.val, lt_trans i.isLt j.isLt⟩).toLinearMap.comp
      (e.repr.toLinearEquiv.toLinearMap.comp V))
  have hdim : Module.finrank ℝ (Fin j.val → ℝ) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (j.val+1))) := by simp
  obtain ⟨z,hz,hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hVz : V z ≠ 0 := by
    intro heq
    apply hzne
    apply spectralHeadEmbedding_injective S hS hn j
    simpa only [map_zero] using heq
  have hhead : ∀ i : Fin n, i < j → e.repr (V z) i = 0 := by
    intro i hij
    have hh := congrFun (LinearMap.mem_ker.mp hz) ⟨i.val,hij⟩
    simpa only [f, LinearMap.pi_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, EuclideanSpace.coe_proj,
      Pi.zero_apply] using hh
  have hlo := eigenbasis_head_bound S hS hn j (V z)
    (fun i hi => spectralHeadEmbedding_tail_zero S hS hn j z i hi)
  have hhi := htail (V z) hhead
  have hp : 0 < ⟪V z,V z⟫_ℝ := real_inner_self_pos.mpr hVz
  exact (mul_le_mul_iff_left₀ hp).mp (hlo.trans hhi)

theorem eigenbasis_tail_square_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hpos : ∀ i, 0 ≤ hT.eigenvalues hn i)
    (j : Fin n) (v : E)
    (hhead : ∀ i : Fin n, i < j → (hT.eigenvectorBasis hn).repr v i = 0) :
    ⟪v,T (T v)⟫_ℝ ≤ (hT.eigenvalues hn j)^2*⟪v,v⟫_ℝ := by
  rw [eigenbasis_inner_apply_sq T hT hn, eigenbasis_inner_self T hT hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hij : i < j
  · rw [hhead i hij]
    simp
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sq_le_sq₀ (hpos i) (hpos j)).mpr
      (hT.eigenvalues_antitone hn (le_of_not_gt hij))

theorem orderedEigenvalue_square_upper (T : Core k) (hT : T.PosSemidef) (j : Fin k) :
    orderedEigenvalue (T*T)
      (by simpa only [← Matrix.conjTranspose_eq_transpose_of_trivial, hT.isHermitian.eq] using
        (Matrix.posSemidef_self_mul_conjTranspose T).isHermitian) j ≤
      (orderedEigenvalue T hT.isHermitian j)^2 := by
  have hS : (T*T).IsHermitian := by
    have ht : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.isHermitian.eq
    simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, ht]
  apply eigenvalue_upper_of_tail_form (T*T).toEuclideanLin T.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian)
    finrank_euclideanSpace_fin j
  intro v hv
  rw [Matrix.toLpLin_mul, LinearMap.comp_apply]
  apply eigenbasis_tail_square_bound T.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT.isHermitian)
    finrank_euclideanSpace_fin _ j v hv
  intro i
  exact orderedEigenvalue_nonneg T hT i

end
end HierarchicalAbsoluteSpectral
