import HierarchicalAbsoluteSpectral.MinMaxInertia
import HierarchicalAbsoluteSpectral.ThresholdRitz
import HierarchicalAbsoluteSpectral.StrongFilterMasks

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {k h : ℕ}

def diagonalPositiveCount (d : Fin k → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => 0 < d i)).card

theorem diagonal_inner (d : Fin k → ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    ⟪v,(Matrix.diagonal d).toEuclideanLin v⟫_ℝ = ∑ i, d i*(v i)^2 := by
  rw [← quadratic_eq_inner]
  simp only [quadratic, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coordinate_compression_diagonal (e : Fin h ↪ Fin k) (d : Fin k → ℝ) :
    (columnEmbedding e)ᵀ*Matrix.diagonal d*columnEmbedding e =
      Matrix.diagonal (fun i => d (e i)) := by
  calc
    _ = (columnEmbedding e)ᵀ*(Matrix.diagonal d*columnEmbedding e) := by rw [Matrix.mul_assoc]
    _ = (columnEmbedding e)ᵀ*(columnEmbedding e*Matrix.diagonal (fun i => d (e i))) := by
      rw [← columnEmbedding_diagonal_intertwines]
    _ = _ := by rw [← Matrix.mul_assoc, columnEmbedding_gram, Matrix.one_mul]

/-- A diagonal form's exact positive pivot count is its number of positive
sorted eigenvalues, including zero and repeated diagonal entries. -/
theorem diagonal_eigenvalue_pos_iff (d : Fin k → ℝ) (j : Fin k) :
    0 < orderedEigenvalue (Matrix.diagonal d) (Matrix.isHermitian_diagonal d) j ↔
      j.val < diagonalPositiveCount d := by
  classical
  let s := Finset.univ.filter (fun i => 0 < d i)
  let T := (Matrix.diagonal d).toEuclideanLin
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal d)
  constructor
  · intro hj
    by_contra hcount
    have hdim : s.card ≤ j.val := by
      simpa only [s, diagonalPositiveCount] using Nat.le_of_not_gt hcount
    let V := spectralHeadEmbedding T hT finrank_euclideanSpace_fin j
    let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] (s → ℝ) :=
      LinearMap.pi (fun i => (EuclideanSpace.proj i.val).toLinearMap)
    let f := L.comp V
    have hlt : Module.finrank ℝ (s → ℝ) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (j.val+1))) := by
      simpa using Nat.lt_succ_of_le hdim
    obtain ⟨z,hz,hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
    have hVz : V z ≠ 0 := by
      intro heq
      apply hzne
      apply spectralHeadEmbedding_injective T hT finrank_euclideanSpace_fin j
      simpa only [map_zero] using heq
    have hhead := eigenbasis_head_bound T hT finrank_euclideanSpace_fin j (V z)
      (fun i hi => spectralHeadEmbedding_tail_zero T hT finrank_euclideanSpace_fin j z i hi)
    have hpositive : 0 < ⟪V z,T (V z)⟫_ℝ :=
      (mul_pos hj (real_inner_self_pos.mpr hVz)).trans_le hhead
    have hzero (i : Fin k) (hi : 0 < d i) : V z i = 0 := by
      have hm : i ∈ s := by simp [s,hi]
      have hh := congrFun (LinearMap.mem_ker.mp hz) ⟨i,hm⟩
      simpa only [f, L, LinearMap.comp_apply, LinearMap.pi_apply,
        ContinuousLinearMap.coe_coe, EuclideanSpace.coe_proj, Pi.zero_apply] using hh
    have hnonpos : ⟪V z,T (V z)⟫_ℝ ≤ 0 := by
      rw [show T = (Matrix.diagonal d).toEuclideanLin from rfl, diagonal_inner]
      apply Finset.sum_nonpos
      intro i hi
      by_cases hp : 0 < d i
      · rw [hzero i hp]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (sq_nonneg _)
    linarith
  · intro hj
    have hdim : j.val+1 ≤ s.card := Nat.succ_le_of_lt hj
    let c : Fin (j.val+1) ↪ Fin s.card := ⟨Fin.castLE hdim,Fin.castLE_injective hdim⟩
    let inclusion : s ↪ Fin k := ⟨Subtype.val,Subtype.val_injective⟩
    let e : Fin (j.val+1) ↪ Fin k := (c.trans s.equivFin.symm.toEmbedding).trans inclusion
    have hde (i : Fin (j.val+1)) : 0 < d (e i) := by
      exact (Finset.mem_filter.mp (s.equivFin.symm (c i)).property).2
    let V := (columnEmbedding e).toEuclideanLin
    apply eigenvalue_pos_of_injective_form T hT finrank_euclideanSpace_fin j V
      (orthonormal_toEuclideanLin_injective _ (columnEmbedding_gram e))
    intro z hz
    obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hh
      push_neg at hh
      apply hz
      apply PiLp.ext
      exact hh
    have hp : 0 < ∑ i, d (e i)*(z i)^2 := by
      exact (mul_pos (hde i) (sq_pos_of_ne_zero hi)).trans_le
        (Finset.single_le_sum (fun i hi => mul_nonneg (hde i).le (sq_nonneg _)) (Finset.mem_univ i))
    change 0 < ⟪(columnEmbedding e).toEuclideanLin z,
      (Matrix.diagonal d).toEuclideanLin ((columnEmbedding e).toEuclideanLin z)⟫_ℝ
    rw [← quadratic_eq_inner, ← quadratic_compression, coordinate_compression_diagonal,
      quadratic_eq_inner, diagonal_inner]
    exact hp

end
end HierarchicalAbsoluteSpectral
