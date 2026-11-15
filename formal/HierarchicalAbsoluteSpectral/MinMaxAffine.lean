import HierarchicalAbsoluteSpectral.MinMaxSquare

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open WithLp
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

theorem eigenvalue_upper_of_kernel_form (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) (c : ℝ)
    (L : E →ₗ[ℝ] (Fin j.val → ℝ))
    (htail : ∀ v, L v = 0 → ⟪v,S v⟫_ℝ ≤ c*⟪v,v⟫_ℝ) :
    hS.eigenvalues hn j ≤ c := by
  let V := spectralHeadEmbedding S hS hn j
  let f := L.comp V
  have hdim : Module.finrank ℝ (Fin j.val → ℝ) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (j.val+1))) := by simp
  obtain ⟨z,hz,hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hVz : V z ≠ 0 := by
    intro heq
    apply hzne
    apply spectralHeadEmbedding_injective S hS hn j
    simpa only [map_zero] using heq
  have hlo := eigenbasis_head_bound S hS hn j (V z)
    (fun i hi => spectralHeadEmbedding_tail_zero S hS hn j z i hi)
  have hhi := htail (V z) (LinearMap.mem_ker.mp hz)
  exact (mul_le_mul_iff_left₀ (real_inner_self_pos.mpr hVz)).mp (hlo.trans hhi)

/-- The descending j-th eigenvalue of `I-C` is one minus the ascending
j-th eigenvalue of `C`. This explicitly connects the safe query and the
near-threshold theorem's two opposite index orders. -/
theorem eigenvalues_id_sub (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) :
    (LinearMap.IsSymmetric.id.sub hC).eigenvalues hn j = 1-hC.eigenvalues hn j.rev := by
  let S : E →ₗ[ℝ] E := LinearMap.id-C
  let hS := LinearMap.IsSymmetric.id.sub hC
  apply le_antisymm
  · let e := hC.eigenvectorBasis hn
    let L : E →ₗ[ℝ] (Fin j.val → ℝ) := LinearMap.pi (fun i =>
      (EuclideanSpace.proj (Fin.rev ⟨i.val,lt_trans i.isLt j.isLt⟩)).toLinearMap.comp
        e.repr.toLinearEquiv.toLinearMap)
    apply eigenvalue_upper_of_kernel_form S hS hn j (1-hC.eigenvalues hn j.rev) L
    intro v hv
    have htail : ∀ i : Fin n, j.rev < i → e.repr v i = 0 := by
      intro i hi
      have hir : i.rev < j := by simpa using Fin.rev_lt_rev.mpr hi
      have hh := congrFun hv ⟨i.rev.val,hir⟩
      have hind : (Fin.rev (⟨i.rev.val,lt_trans hir j.isLt⟩ : Fin n)) = i := by
        have heq : (⟨i.rev.val,lt_trans hir j.isLt⟩ : Fin n) = i.rev := Fin.ext rfl
        rw [heq, Fin.rev_rev]
      simpa only [L, LinearMap.pi_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, EuclideanSpace.coe_proj,
        hind, Pi.zero_apply] using hh
    have hh := eigenbasis_head_bound C hC hn j.rev v htail
    change ⟪v,(LinearMap.id-C : E →ₗ[ℝ] E) v⟫_ℝ ≤ _
    simp only [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right]
    nlinarith
  · let V := spectralBottomEmbedding C hC hn j
    apply eigenvalue_lower_of_injective_form S hS hn j V
      (spectralBottomEmbedding_injective C hC hn j)
    intro z
    have hh := eigenbasis_tail_bound C hC hn j.rev (V z)
      (fun i hi => spectralBottomEmbedding_head_zero C hC hn j z i hi)
    change _ ≤ ⟪V z,(LinearMap.id-C : E →ₗ[ℝ] E) (V z)⟫_ℝ
    simp only [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right]
    nlinarith

end
end HierarchicalAbsoluteSpectral
