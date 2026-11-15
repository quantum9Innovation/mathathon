import HierarchicalAbsoluteSpectral.MainStatementsProbabilityAssembly
import HierarchicalAbsoluteSpectral.MainCoreProbabilityAssembly

/-! The original-input probability theorem for the actual fixed-depth program.
`tailSingularValue (I.A * I.B) r` is the (r+1)-st singular value, since Lean
indices start at zero. No successful sketch, hierarchy, oracle or filter
certificate occurs among the theorem's hypotheses. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] fixedDepthProgram

theorem fixedDepthProgram_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, (fixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(fixedDepthProgram kernels I g).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  apply fixedDepthProgram_good_event_of_core_events kernels I
  intro z hz
  let S := mainSketchFromFiniteSample I z
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  exact mainCoreProgramFromOriginalTape_good_event kernels I S hz C

theorem fixedDepthProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖I.A*I.B-(fixedDepthProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I
  exact hEp.trans (measureReal_mono (fun g hg => (hE g hg).2))

theorem fixedDepthProgram_rank_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      (fixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(fixedDepthProgram kernels I g).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I
  exact hEp.trans (measureReal_mono (fun g hg => hE g hg))

end
end HierarchicalAbsoluteSpectral
