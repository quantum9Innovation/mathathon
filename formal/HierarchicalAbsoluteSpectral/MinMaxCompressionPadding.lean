import HierarchicalAbsoluteSpectral.MassSpectrumSingular
import HierarchicalAbsoluteSpectral.ThresholdRitzTests

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped MatrixOrder
variable {k w : ℕ}

theorem sq_tailSingularValue_eq_gram {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    tailSingularValue M j.val^2 = orderedEigenvalue (Mᵀ*M)
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian) j := by
  have hh := M.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace_fin j
  simpa only [tailSingularValue,orderedEigenvalue,matrix_adjoint_gram] using hh

theorem orderedEigenvalue_orthogonal_padding (C : Core w) (hC : C.PosSemidef)
    (U : Matrix (Fin k) (Fin w) ℝ) (hU : Uᵀ*U = 1) (j : Fin k) :
    orderedEigenvalue (U*C*Uᵀ)
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
        (hC.conjTranspose_mul_mul_same Uᵀ).isHermitian) j =
      if hjw : j.val < w then orderedEigenvalue C hC.isHermitian ⟨j.val,hjw⟩ else 0 := by
  let Y := U*CFC.sqrt C
  have hgram : Yᵀ*Y = C := by
    calc
      _ = CFC.sqrt C*(Uᵀ*U)*CFC.sqrt C := by simp only [Y,Matrix.transpose_mul,massRoot_transpose,Matrix.mul_assoc]
      _ = C := by rw [hU,Matrix.mul_one,CFC.sqrt_mul_sqrt_self C hC.nonneg]
  have hreverse : Y*Yᵀ = U*C*Uᵀ := by
    calc
      _ = U*(CFC.sqrt C*CFC.sqrt C)*Uᵀ := by simp only [Y,Matrix.transpose_mul,massRoot_transpose,Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self C hC.nonneg]
  split_ifs with hjw
  · have h₁ := sq_tailSingularValue_eq_reverseGram Y j.val j.isLt hjw
    have h₂ := sq_tailSingularValue_eq_gram Y ⟨j.val,hjw⟩
    have heq := h₁.symm.trans h₂
    simpa only [hgram,hreverse] using heq
  · have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin w)) ≤ j.val := by
      simpa only [finrank_euclideanSpace_fin] using Nat.le_of_not_gt hjw
    have hrange : Module.finrank ℝ Yᵀ.toEuclideanLin.range ≤ j.val :=
      (Submodule.finrank_le _).trans hdim
    have hz : tailSingularValue Yᵀ j.val = 0 :=
      Yᵀ.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr hrange
    have hs := sq_tailSingularValue_eq_gram Yᵀ j
    rw [hz] at hs
    simpa only [Matrix.transpose_transpose,hreverse,zero_pow (by decide : (2:ℕ) ≠ 0)] using hs.symm

theorem KrylovQueryData.ritzValue_eq_projector {r q : ℕ} {T : Core k}
    {Ω : Matrix (Fin k) (Fin r) ℝ} (data : KrylovQueryData T Ω q) (j : Fin k) :
    let U := data.range.basis
    let P := U*Uᵀ
    data.ritzValue j = orderedEigenvalue (P*(T*T)*P)
      (by
        have hh := data.compression_posSemidef.conjTranspose_mul_mul_same Uᵀ
        simpa only [U,P,data.compression_eq,Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.transpose_transpose,Matrix.mul_assoc] using hh.isHermitian) j := by
  have hh := orderedEigenvalue_orthogonal_padding data.compression data.compression_posSemidef
    data.range.basis data.range.orthogonal j
  dsimp only
  symm
  simpa only [KrylovQueryData.ritzValue,data.compression_eq,Matrix.mul_assoc] using hh

end
end HierarchicalAbsoluteSpectral
