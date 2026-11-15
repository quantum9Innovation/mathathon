import HierarchicalAbsoluteSpectral.ThresholdKrylovMeasurable
import HierarchicalAbsoluteSpectral.ThresholdOptionalInertia

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k r : ℕ}

/-- Form the fixed-size Ritz matrix from TU and U, without materializing T.
Its equality certificate supplies a jointly measurable semantic value. -/
def krylovFullMatrixProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    ArithmeticProgram {M : Core k // M = krylovRitzFixedMatrix kernels T q Ω} := do
  let data ← (krylovQueryDataProgram kernels T hT actions q Ω).certify
  let U := data.val.range.basis
  let UC ← ((kernels k data.val.range.dimension data.val.range.dimension).program U data.val.compression).certify
  let M ← ((kernels k data.val.range.dimension k).program UC.val Uᵀ).certify
  have hr : data.val.range = (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).eval :=
    (congrArg KrylovQueryData.range data.property).trans
      (krylovQueryDataProgram_range_eq kernels T hT actions q Ω)
  have hp : U*Uᵀ = krylovSpanProjector kernels T q Ω :=
    congrArg (fun out : OrthogonalRange (flatBlockKrylov T Ω q) => out.basis*out.basisᵀ) hr
  have hM : M.val = krylovRitzFixedMatrix kernels T q Ω := by
    calc
      M.val = UC.val*Uᵀ := M.property.trans (ArithmeticKernel.program_eval _ _ _)
      _ = (U*data.val.compression)*Uᵀ := by rw [UC.property,ArithmeticKernel.program_eval]
      _ = (U*Uᵀ)*(T*T)*(U*Uᵀ) := by
        rw [data.val.compression_eq]
        simp only [U,Matrix.mul_assoc]
      _ = krylovRitzFixedMatrix kernels T q Ω := by rw [hp]; rfl
  .pure ⟨M.val,hM⟩

theorem krylovFullMatrixProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovFullMatrixProgram kernels T hT actions q Ω).admissible := by
  simp only [krylovFullMatrixProgram,admissible_bind,certify_admissible,
    krylovQueryDataProgram_admissible,ArithmeticKernel.program_admissible,admissible_pure,and_self]

theorem krylovFullMatrixProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    let w := (krylovQueryDataProgram kernels T hT actions q Ω).eval.range.dimension
    (krylovFullMatrixProgram kernels T hT actions q Ω).work =
      (krylovQueryDataProgram kernels T hT actions q Ω).work+(kernels k w w).cost+(kernels k w k).cost := by
  dsimp only
  simp only [krylovFullMatrixProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,add_zero]
  rw [(krylovQueryDataProgram kernels T hT actions q Ω).certify.eval.property]
  omega

def gaussianKrylovFullMatrixProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) :
    ArithmeticProgram {M : Core k // M = krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix G)} := do
  let Ω ← (source.program (columnsMatrix G)).certify
  let M ← krylovFullMatrixProgram kernels T hT actions q Ω.val
  .pure ⟨M.val,by rw [M.property,Ω.property,source.correct]⟩

theorem gaussianKrylovFullMatrixProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) :
    (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).admissible := by
  simp only [gaussianKrylovFullMatrixProgram,admissible_bind,certify_admissible,
    source.valid,krylovFullMatrixProgram_admissible,admissible_pure,and_self]

end
end HierarchicalAbsoluteSpectral
