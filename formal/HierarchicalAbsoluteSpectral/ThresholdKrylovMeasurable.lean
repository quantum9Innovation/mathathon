import HierarchicalAbsoluteSpectral.MinMaxCompressionPadding
import HierarchicalAbsoluteSpectral.MinMaxProjectorMeasurable
import HierarchicalAbsoluteSpectral.ThresholdKrylovGaussian

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}

local instance krylovMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance krylovMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

theorem orthogonalRangeProgram_transport (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b : ℕ} {Y Z : Matrix (Fin a) (Fin b) ℝ} (h : Y = Z) :
    (h ▸ (orthogonalRangeProgram kernels Y).eval) =
      (orthogonalRangeProgram kernels Z).eval := by
  cases h
  rfl

theorem krylovRangeProgram_eval_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (action : MatrixAction T r) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovRangeProgram kernels T action q Ω).eval =
      (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).eval := by
  simp only [krylovRangeProgram,ArithmeticProgram.eval_bind,ArithmeticProgram.eval_pure]
  exact orthogonalRangeProgram_transport kernels _

theorem krylovQueryDataProgram_range_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovQueryDataProgram kernels T hT actions q Ω).eval.range =
      (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).eval := by
  simp only [krylovQueryDataProgram,ArithmeticProgram.eval_bind,ArithmeticProgram.eval_pure]
  exact krylovRangeProgram_eval_eq kernels T (actions r) q Ω

def krylovSpanProjector (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) : Core k :=
  let out := (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).eval
  out.basis*out.basisᵀ

theorem krylovSpanProjector_transpose (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovSpanProjector kernels T q Ω)ᵀ = krylovSpanProjector kernels T q Ω := by
  simp only [krylovSpanProjector,Matrix.transpose_mul,Matrix.transpose_transpose]

def krylovRitzFixedMatrix (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) : Core k :=
  krylovSpanProjector kernels T q Ω*(T*T)*krylovSpanProjector kernels T q Ω

theorem krylovRitzFixedMatrix_isHermitian (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) :
    (krylovRitzFixedMatrix kernels T q Ω).IsHermitian := by
  have hh := compression_isHermitian (T*T) (square_isHermitian T hT) (krylovSpanProjector kernels T q Ω)
  simpa only [krylovRitzFixedMatrix,krylovSpanProjector_transpose] using hh

theorem krylovQueryDataProgram_ritzValue_eq_fixed (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin r) ℝ) (j : Fin k) :
    (krylovQueryDataProgram kernels T hT actions q Ω).eval.ritzValue j =
      orderedEigenvalue (krylovRitzFixedMatrix kernels T q Ω)
        (krylovRitzFixedMatrix_isHermitian kernels T hT q Ω) j := by
  let data := (krylovQueryDataProgram kernels T hT actions q Ω).eval
  have hr : data.range = (orthogonalRangeProgram kernels (flatBlockKrylov T Ω q)).eval :=
    krylovQueryDataProgram_range_eq kernels T hT actions q Ω
  have hp : data.range.basis*data.range.basisᵀ = krylovSpanProjector kernels T q Ω :=
    congrArg (fun out : OrthogonalRange (flatBlockKrylov T Ω q) => out.basis*out.basisᵀ) hr
  have hh := data.ritzValue_eq_projector j
  dsimp only at hh
  simpa only [hp,krylovRitzFixedMatrix] using hh

theorem flatBlockKrylov_continuous (q : ℕ) :
    Continuous (fun x : Core k × Matrix (Fin k) (Fin r) ℝ => flatBlockKrylov x.1 x.2 q) := by
  apply continuous_matrix
  intro i s
  change Continuous (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
    (x.1^(finProdFinEquiv.symm s).1.val*x.2) i (finProdFinEquiv.symm s).2)
  exact ((continuous_fst.pow _).matrix_mul continuous_snd).matrix_elem _ _

theorem krylovSpanProjector_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (q : ℕ) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ => krylovSpanProjector kernels x.1 q x.2) :=
  orthogonalRangeProgram_projector_measurable kernels |>.comp (flatBlockKrylov_continuous q).measurable

theorem krylovRitzFixedMatrix_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (q : ℕ) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ => krylovRitzFixedMatrix kernels x.1 q x.2) :=
  ((krylovSpanProjector_measurable kernels q).mul (measurable_fst.mul measurable_fst)).mul
    (krylovSpanProjector_measurable kernels q)

end
end HierarchicalAbsoluteSpectral
