import HierarchicalAbsoluteSpectral.CoarseAlgebraRange
import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDProgram

/-! Exact range extraction with zero-rank deflation, executed by finite
field arithmetic, scalar roots, comparisons and verified matrix kernels. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {m w : ℕ}

def orthogonalRangeProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Y : Matrix (Fin m) (Fin w) ℝ) : ArithmeticProgram (OrthogonalRange Y) := do
  let G ← certify ((kernels w m w).program Yᵀ Y)
  have hG : G.val = Yᵀ*Y := G.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hGpos : G.val.PosSemidef := by
    rw [hG]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self Y
  let p ← psdGramProgram kernels w G.val hGpos
  let Q ← certify ((kernels m w p.dimension).program Y p.leftInverseᵀ)
  let expected := rangeFromPSDGramOfEq Y p hG
  ArithmeticProgram.pure (expected.replaceBasis Q.val (by
    dsimp only [expected, rangeFromPSDGramOfEq]
    exact Q.property.trans (ArithmeticKernel.program_eval _ _ _)))

theorem orthogonalRangeProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Y : Matrix (Fin m) (Fin w) ℝ) : (orthogonalRangeProgram kernels Y).admissible := by
  simp only [orthogonalRangeProgram, admissible_bind, certify_admissible,
    ArithmeticKernel.program_admissible, psdGramProgram_admissible, admissible_pure, and_self]

theorem orthogonalRangeProgram_correct (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Y : Matrix (Fin m) (Fin w) ℝ) :
    let out := (orthogonalRangeProgram kernels Y).eval
    out.basisᵀ*out.basis = 1 ∧ Y = out.basis*out.coefficients ∧
      out.dimension = Y.rank ∧ out.dimension ≤ m ∧ out.dimension ≤ w := by
  exact ⟨(orthogonalRangeProgram kernels Y).eval.orthogonal,
    (orthogonalRangeProgram kernels Y).eval.spans,
    (orthogonalRangeProgram kernels Y).eval.dimension_eq_rank,
    (orthogonalRangeProgram kernels Y).eval.dimension_le_rows,
    (orthogonalRangeProgram kernels Y).eval.dimension_le_cols⟩

theorem OrthogonalRange.projection_exact {Y : Matrix (Fin m) (Fin w) ℝ} (out : OrthogonalRange Y) :
    out.basis*out.basisᵀ*Y = Y := by
  calc
    _ = out.basis*out.basisᵀ*(out.basis*out.coefficients) :=
      congrArg (out.basis*out.basisᵀ*·) out.spans
    _ = out.basis*(out.basisᵀ*out.basis)*out.coefficients := by
      simp only [Matrix.mul_assoc]
    _ = Y := by rw [out.orthogonal, Matrix.mul_one, ← out.spans]

end
end HierarchicalAbsoluteSpectral
