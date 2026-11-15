import HierarchicalAbsoluteSpectral.StrongFilterDiagonal

/-! An actual orthonormal basis of any filtered range, with both span maps.
Dependent and zero columns automatically reduce the output width. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

theorem orthonormal_range_factorization {k r : ℕ}
    (Y : Matrix (Fin k) (Fin r) ℝ) :
    ∃ w : ℕ, w ≤ r ∧ ∃ U : Matrix (Fin k) (Fin w) ℝ,
      Uᵀ*U = 1 ∧ ∃ W : Matrix (Fin w) (Fin r) ℝ,
        ∃ X : Matrix (Fin r) (Fin w) ℝ, Y = U*W ∧ U = Y*X := by
  let f := Y.toEuclideanLin
  let V := f.range
  let w := Module.finrank ℝ V
  let b := stdOrthonormalBasis ℝ V
  let U : Matrix (Fin k) (Fin w) ℝ := fun i j => (b j).val i
  have hw : w ≤ r := by
    have hh := f.finrank_range_le
    simpa only [w, V, finrank_euclideanSpace, Fintype.card_fin] using hh
  have hU : Uᵀ*U = 1 := by
    ext i j
    have h := (orthonormal_iff_ite.mp b.orthonormal) i j
    rw [Submodule.coe_inner] at h
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    change (∑ a, (b i).val a*(b j).val a) = if i = j then 1 else 0
    have heq : (∑ a, (b i).val a*(b j).val a) = ∑ a, (b j).val a*(b i).val a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [heq]
    exact h
  let y : Fin r → V := fun j => ⟨f (EuclideanSpace.single j 1), ⟨_,rfl⟩⟩
  let W : Matrix (Fin w) (Fin r) ℝ := fun i j => b.repr (y j) i
  have hY : Y = U*W := by
    ext i j
    have h := congrArg (fun v : V => v.val i) (b.sum_repr (y j))
    have hy : (y j).val i = Y i j := by
      simp [y, f, Matrix.toEuclideanLin_apply, EuclideanSpace.single, Matrix.mulVec_single]
    rw [hy] at h
    simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at h
    calc
      _ = ∑ a, b.repr (y j) a*(b a).val i := h.symm
      _ = ∑ a, (b a).val i*b.repr (y j) a :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = _ := rfl
  have hpre : ∀ j : Fin w, ∃ x : EuclideanSpace ℝ (Fin r), f x = (b j).val :=
    fun j => (b j).property
  choose x hx using hpre
  let X : Matrix (Fin r) (Fin w) ℝ := fun i j => x j i
  have hX : U = Y*X := by
    ext i j
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v i) (hx j)
    simpa only [U, X, f, Matrix.toEuclideanLin_apply, ofLp_toLp,
      Matrix.mul_apply, Matrix.mulVec, dotProduct] using h.symm
  exact ⟨w,hw,U,hU,W,X,hY,hX⟩

end
end HierarchicalAbsoluteSpectral
