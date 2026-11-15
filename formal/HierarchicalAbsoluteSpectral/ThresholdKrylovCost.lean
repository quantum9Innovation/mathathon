import HierarchicalAbsoluteSpectral.ThresholdKrylovProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraWideCost

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {k r : ℕ}

theorem krylovRangeProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (action : MatrixAction T r) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ)
    (rangeCap : ℕ) (hRange : (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).work ≤ rangeCap) :
    (krylovRangeProgram kernels T action q Ω).work ≤ q*action.cost+rangeCap := by
  simp only [krylovRangeProgram, work_bind, certify_work, work_pure, add_zero]
  have hb := krylovBlocksProgram_work_le action.program action.cost action.work_le q Ω
  have hblocks : (krylovBlocksProgram action.program q Ω).certify.eval.val =
      (fun s => T^s.val*Ω) := (krylovBlocksProgram action.program q Ω).certify.eval.property.trans
    (krylovBlocksProgram_eval T action.program action.correct q Ω)
  rw [hblocks]
  exact Nat.add_le_add hb hRange

theorem krylovQueryDataProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    let out := (krylovRangeProgram kernels T (actions r) q Ω).eval
    (krylovQueryDataProgram kernels T hT actions q Ω).work ≤
      (krylovRangeProgram kernels T (actions r) q Ω).work+
        (actions out.dimension).cost+(kernels out.dimension k out.dimension).cost := by
  simp only [krylovQueryDataProgram, work_bind, certify_work, ArithmeticKernel.program_work,
    work_pure, add_zero]
  have hh := (actions (krylovRangeProgram kernels T (actions r) q Ω).eval.dimension).work_le
    (krylovRangeProgram kernels T (actions r) q Ω).eval.basis
  omega

theorem krylovQueryDataProgram_width_caps (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    let out := (krylovQueryDataProgram kernels T hT actions q Ω).eval
    out.range.dimension ≤ k ∧ out.range.dimension ≤ (q+1)*r := by
  exact ⟨(krylovQueryDataProgram kernels T hT actions q Ω).eval.range.dimension_le_rows,
    (krylovQueryDataProgram kernels T hT actions q Ω).eval.range.dimension_le_cols⟩

end
end HierarchicalAbsoluteSpectral
