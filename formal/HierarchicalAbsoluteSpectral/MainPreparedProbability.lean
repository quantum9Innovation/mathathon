import HierarchicalAbsoluteSpectral.MainPreparedProgram
import HierarchicalAbsoluteSpectral.MainStatementsProbability

/-! Original-input probability guarantees for the program that executes
all derived scalar parameter calculations. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem preparedFixedDepthProgram_rank_error_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, (preparedFixedDepthProgram kernels I g).eval.width ≤ r ∧
        (preparedFixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(preparedFixedDepthProgram kernels I g).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  rw [preparedFixedDepthProgram_eval]
  exact ⟨(fixedDepthProgram kernels I g).eval.width_le,hE g hg⟩

theorem preparedFixedDepthProgram_rank_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      (preparedFixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
      ‖I.A*I.B-(preparedFixedDepthProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  simpa only [preparedFixedDepthProgram_eval] using fixedDepthProgram_rank_error_probability kernels I

end
end HierarchicalAbsoluteSpectral
