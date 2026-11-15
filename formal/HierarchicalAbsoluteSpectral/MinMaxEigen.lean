import HierarchicalAbsoluteSpectral.Spectral
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Variational comparison for the actual sorted self-adjoint eigenvalues.
Indices are zero based. The proof uses an explicit finite-dimensional
kernel argument, so no min--max theorem is assumed as an extra axiom.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open WithLp
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

theorem eigenbasis_inner_self (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (v : E) :
    ⟪v,v⟫_ℝ = ∑ i : Fin n, ((hT.eigenvectorBasis hn).repr v i)^2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v v, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem eigenbasis_inner_apply (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (v : E) :
    ⟪v,T v⟫_ℝ = ∑ i : Fin n, hT.eigenvalues hn i*((hT.eigenvectorBasis hn).repr v i)^2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v (T v), PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem eigenbasis_tail_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) (v : E)
    (hhead : ∀ i : Fin n, i < j → (hT.eigenvectorBasis hn).repr v i = 0) :
    ⟪v,T v⟫_ℝ ≤ hT.eigenvalues hn j*⟪v,v⟫_ℝ := by
  rw [eigenbasis_inner_apply T hT hn, eigenbasis_inner_self T hT hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hij : i < j
  · rw [hhead i hij]
    simp
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (le_of_not_gt hij)) (sq_nonneg _)

/-- A j+1 dimensional injected space with Rayleigh quotient at least c
forces the zero-indexed j-th eigenvalue to be at least c. -/
theorem eigenvalue_lower_of_injective_form (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n)
    (V : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] E) (hV : Function.Injective V)
    (c : ℝ) (hform : ∀ z, c*⟪V z,V z⟫_ℝ ≤ ⟪V z,T (V z)⟫_ℝ) :
    c ≤ hT.eigenvalues hn j := by
  let e := hT.eigenvectorBasis hn
  let f : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] (Fin j.val → ℝ) :=
    LinearMap.pi (fun i => (EuclideanSpace.proj ⟨i.val, lt_trans i.isLt j.isLt⟩).toLinearMap.comp
      (e.repr.toLinearEquiv.toLinearMap.comp V))
  have hdim : Module.finrank ℝ (Fin j.val → ℝ) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (j.val+1))) := by simp
  obtain ⟨z, hz, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hVz : V z ≠ 0 := by
    intro heq
    apply hzne
    apply hV
    simpa only [map_zero] using heq
  have hhead : ∀ i : Fin n, i < j → e.repr (V z) i = 0 := by
    intro i hij
    have h := congrFun (LinearMap.mem_ker.mp hz) ⟨i.val, hij⟩
    simpa only [f, LinearMap.pi_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe, EuclideanSpace.coe_proj,
      Pi.zero_apply] using h
  have htail := eigenbasis_tail_bound T hT hn j (V z) hhead
  have hpos : 0 < ⟪V z,V z⟫_ℝ := real_inner_self_pos.mpr hVz
  exact (mul_le_mul_iff_left₀ hpos).mp ((hform z).trans htail)

def spectralHeadIndex (j : Fin n) (i : Fin (j.val+1)) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt j.isLt)⟩

def spectralHeadInclude (j : Fin n) :
    EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun z := toLp 2 (fun i => if hi : i.val ≤ j.val then z ⟨i.val, by omega⟩ else 0)
  map_add' z w := by
    apply PiLp.ext
    intro i
    by_cases hi : i.val ≤ j.val
    · have hf : i ≤ j := hi
      simp [hi, hf]
    · have hf : ¬i ≤ j := hi
      simp [hi, hf]
  map_smul' r z := by
    apply PiLp.ext
    intro i
    by_cases hi : i.val ≤ j.val
    · have hf : i ≤ j := hi
      simp [hi, hf]
    · have hf : ¬i ≤ j := hi
      simp [hi, hf]

theorem spectralHeadInclude_coordinate (j : Fin n) (z : EuclideanSpace ℝ (Fin (j.val+1)))
    (i : Fin (j.val+1)) : spectralHeadInclude j z (spectralHeadIndex j i) = z i := by
  have hi : i.val ≤ j.val := Nat.le_of_lt_succ i.isLt
  simp only [spectralHeadInclude, LinearMap.coe_mk, AddHom.coe_mk, ofLp_toLp,
    spectralHeadIndex, hi, ↓reduceDIte]

theorem spectralHeadInclude_injective (j : Fin n) : Function.Injective (spectralHeadInclude j) := by
  intro z w h
  apply PiLp.ext
  intro i
  have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x (spectralHeadIndex j i)) h
  simpa only [spectralHeadInclude_coordinate] using hh

theorem eigenbasis_head_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) (v : E)
    (htail : ∀ i : Fin n, j < i → (hT.eigenvectorBasis hn).repr v i = 0) :
    hT.eigenvalues hn j*⟪v,v⟫_ℝ ≤ ⟪v,T v⟫_ℝ := by
  rw [eigenbasis_inner_apply T hT hn, eigenbasis_inner_self T hT hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hij : j < i
  · rw [htail i hij]
    simp
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (le_of_not_gt hij)) (sq_nonneg _)

def spectralHeadEmbedding (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) : EuclideanSpace ℝ (Fin (j.val+1)) →ₗ[ℝ] E :=
  (hT.eigenvectorBasis hn).repr.symm.toLinearEquiv.toLinearMap.comp (spectralHeadInclude j)

theorem spectralHeadEmbedding_injective (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n) : Function.Injective (spectralHeadEmbedding T hT hn j) :=
  (hT.eigenvectorBasis hn).repr.symm.injective.comp (spectralHeadInclude_injective j)

theorem spectralHeadEmbedding_tail_zero (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (j : Fin n)
    (z : EuclideanSpace ℝ (Fin (j.val+1))) (i : Fin n) (hi : j < i) :
    (hT.eigenvectorBasis hn).repr (spectralHeadEmbedding T hT hn j z) i = 0 := by
  simp only [spectralHeadEmbedding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
  have hnot : ¬i.val ≤ j.val := Nat.not_le.mpr hi
  simp only [spectralHeadInclude, LinearMap.coe_mk, AddHom.coe_mk, ofLp_toLp, hnot, ↓reduceDIte]

theorem eigenvalues_mono_of_inner (S T : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hform : ∀ v, ⟪v,S v⟫_ℝ ≤ ⟪v,T v⟫_ℝ) (j : Fin n) :
    hS.eigenvalues hn j ≤ hT.eigenvalues hn j := by
  apply eigenvalue_lower_of_injective_form T hT hn j (spectralHeadEmbedding S hS hn j)
    (spectralHeadEmbedding_injective S hS hn j)
  intro z
  exact (eigenbasis_head_bound S hS hn j _
    (fun i hi => spectralHeadEmbedding_tail_zero S hS hn j z i hi)).trans (hform _)

end
end HierarchicalAbsoluteSpectral
