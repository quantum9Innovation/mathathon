import HierarchicalAbsoluteSpectral.MassSpectrum

/-! The bottom eigenspace used in the near-threshold transfer is constructed
from the actual spectral basis, with its dimension and Rayleigh bounds proved. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open WithLp
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

theorem eigenbasis_inner_apply_sq (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (v : E) :
    ⟪v,T (T v)⟫_ℝ =
      ∑ i : Fin n, (hT.eigenvalues hn i)^2*((hT.eigenvectorBasis hn).repr v i)^2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v (T (T v)), PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hT.eigenvectorBasis_apply_self_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem eigenvalue_rayleigh (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) :
    ⟪hT.eigenvectorBasis hn j,T (hT.eigenvectorBasis hn j)⟫_ℝ = hT.eigenvalues hn j := by
  rw [hT.apply_eigenvectorBasis]
  simp only [inner_smul_right, RCLike.ofReal_real_eq_id, id_eq, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one, one_pow, mul_one]

theorem eigenvalue_lower_of_form (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (a : ℝ)
    (hform : ∀ v, a*⟪v,v⟫_ℝ ≤ ⟪v,T v⟫_ℝ) (j : Fin n) :
    a ≤ hT.eigenvalues hn j := by
  have hh := hform (hT.eigenvectorBasis hn j)
  simpa only [eigenvalue_rayleigh, real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one,
    one_pow, mul_one] using hh

def spectralBottomEmbedding (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] E :=
  (hT.eigenvectorBasis hn).repr.symm.toLinearEquiv.toLinearMap.comp
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ Fin.revPerm).toLinearEquiv.toLinearMap.comp
      (spectralHeadInclude j))

theorem spectralBottomEmbedding_injective (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) : Function.Injective (spectralBottomEmbedding T hT hn j) :=
  (hT.eigenvectorBasis hn).repr.symm.injective.comp
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ Fin.revPerm).injective.comp
      (spectralHeadInclude_injective j))

theorem spectralBottomEmbedding_head_zero (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n)
    (z : EuclideanSpace ℝ (Fin (j.val+1))) (i : Fin n) (hi : i < j.rev) :
    (hT.eigenvectorBasis hn).repr (spectralBottomEmbedding T hT hn j z) i = 0 := by
  simp only [spectralBottomEmbedding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
  have hnot : ¬i.rev.val ≤ j.val := by
    have hh : j < i.rev := by simpa using (Fin.rev_lt_rev.mpr hi)
    exact Nat.not_le.mpr hh
  have hnot' : ¬i.rev ≤ j := hnot
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Fin.revPerm,
    spectralHeadInclude, hnot, hnot']

theorem spectralBottomEmbedding_near_form (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) (κ α : ℝ)
    (hκ : 1 ≤ κ) (hκ' : κ ≤ 5) (hα : 0 < α) (hα' : α ≤ 1/(100*κ))
    (hlo : ∀ i, -1 ≤ hT.eigenvalues hn i) (hnear : hT.eigenvalues hn j.rev ≤ α)
    (z : EuclideanSpace ℝ (Fin (j.val+1))) :
    let v := spectralBottomEmbedding T hT hn j z
    ⟪v,T v⟫_ℝ ≤ (α/(1-κ*α^2))*(⟪v,v⟫_ℝ-κ*⟪v,T (T v)⟫_ℝ) := by
  dsimp only
  rw [eigenbasis_inner_apply T hT hn, eigenbasis_inner_self T hT hn,
    eigenbasis_inner_apply_sq T hT hn]
  calc
    _ ≤ ∑ i : Fin n, (α/(1-κ*α^2))*(1-κ*(hT.eigenvalues hn i)^2)*
        ((hT.eigenvectorBasis hn).repr (spectralBottomEmbedding T hT hn j z) i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hij : i < j.rev
      · rw [spectralBottomEmbedding_head_zero T hT hn j z i hij]
        simp
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply near_scalar_inequality κ α _ hκ hκ' hα hα' (hlo i)
        exact (hT.eigenvalues_antitone hn (le_of_not_gt hij)).trans hnear
    _ = _ := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end
end HierarchicalAbsoluteSpectral
