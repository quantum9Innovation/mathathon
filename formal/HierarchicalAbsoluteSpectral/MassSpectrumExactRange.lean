import HierarchicalAbsoluteSpectral.MassSpectrumInitializer
import HierarchicalAbsoluteSpectral.SupportReduction

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k p w n : ℕ}

/-- A zero initializer residual gives an exact range for the original right
factor on the coarse lower-sketch event, even when its rank is deficient. -/
theorem initializer_exact_right_range
    (B : Matrix (Fin k) (Fin p) ℝ) (Q₀ : Core k)
    (U : Matrix (Fin k) (Fin w) ℝ) (c : ℝ) (hc : 0<c)
    (hgram : c • (B*Bᵀ) ≤ Q₀) (hspan : Q₀=U*(Uᵀ*Q₀)) :
    B=U*(Uᵀ*B) := by
  let E : Core k := 1-U*Uᵀ
  have hE : Eᵀ=E := by simp only [E,Matrix.transpose_sub,Matrix.transpose_one,
    Matrix.transpose_mul,Matrix.transpose_transpose]
  have hEQ : E*Q₀=0 := by
    dsimp only [E]
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,← hspan,sub_self]
  have hh := support_gram_congruence_mono hgram E
  have heq : E*(B*Bᵀ)*E=(E*B)*(E*B)ᵀ := by
    simp only [Matrix.transpose_mul,hE,Matrix.mul_assoc]
  simp only [Matrix.mul_smul,Matrix.smul_mul,hE,heq,hEQ,Matrix.zero_mul] at hh
  have hp : (0 : Core k) ≤ (E*B)*(E*B)ᵀ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose (E*B)).nonneg
  have hz : c • ((E*B)*(E*B)ᵀ)=0 := le_antisymm hh (smul_nonneg hc.le hp)
  have hEB : E*B=0 := by
    apply Matrix.self_mul_conjTranspose_eq_zero.mp
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (smul_eq_zero.mp hz).resolve_left hc.ne'
  simpa only [E,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,sub_eq_zero] using hEB

theorem initializer_exact_physical_range
    (Z : Matrix (Fin n) (Fin k) ℝ) (B : Matrix (Fin k) (Fin p) ℝ) (Q₀ : Core k)
    (U : Matrix (Fin k) (Fin w) ℝ) (c : ℝ) (hc : 0<c)
    (hgram : c • (B*Bᵀ) ≤ Q₀) (hzero : initializerValue Q₀ U=0)
    (out : OrthogonalRange (Z*U)) :
    out.basis*(out.basisᵀ*(Z*B))=Z*B := by
  have hspan := (initializer_zero_rank Q₀ U (le_refl w) hzero).1
  have hB := initializer_exact_right_range B Q₀ U c hc hgram hspan
  have hproj := congrArg (fun Y : Matrix (Fin n) (Fin w) ℝ => Y*(Uᵀ*B)) out.projection_exact
  simpa only [Matrix.mul_assoc,← hB] using hproj

end
end HierarchicalAbsoluteSpectral
