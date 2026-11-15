import HierarchicalAbsoluteSpectral.MainFamilyProgram
import HierarchicalAbsoluteSpectral.MainStatementsProbability

/-! The growing-depth original-input probability theorem, including the
finite zero-level fallback, for the same executed counted program. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N m r : ℕ}

theorem growingDepthProgram_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FamilyProblem N m r) :
    ∃ E : Set (FamilyRandomTape I), MeasurableSet E ∧ (familyRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, (growingDepthProgram kernels I g).eval.width ≤ r ∧
        (growingDepthProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(growingDepthProgram kernels I g).eval.product‖ ≤
          (1+(m/N : ℝ)^2*Real.sqrt (m/N : ℝ))*tailSingularValue (I.A*I.B) r := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I.prepared.fixed
  refine ⟨E,hEm,?_,?_⟩
  · simpa only [familyRandomLaw,I.prepared.input_failure] using hEp
  · intro g hg
    have hgood := hE g hg
    have hfamily := familySuccessEvent_of_internal kernels I g hgood.2
    exact ⟨(growingDepthProgram kernels I g).eval.width_le,
      (growingDepthProgram kernels I g).eval.rank_le,hfamily⟩

theorem growingDepthProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FamilyProblem N m r) :
    (familyRandomLaw I).real {g : FamilyRandomTape I |
      ‖I.A*I.B-(growingDepthProgram kernels I g).eval.product‖ ≤
        (1+(m/N : ℝ)^2*Real.sqrt (m/N : ℝ))*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := growingDepthProgram_good_event kernels I
  exact hEp.trans (measureReal_mono (fun g hg => (hE g hg).2.2))

end
end HierarchicalAbsoluteSpectral
