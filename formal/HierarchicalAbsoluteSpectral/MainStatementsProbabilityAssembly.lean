import HierarchicalAbsoluteSpectral.MainCoreExtensionality
import HierarchicalAbsoluteSpectral.ProbabilityMainTapeGood

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] fixedDepthProgram mainProgramFromFiniteStateCoreTape

/-- Only an intermediate assembly lemma; the final theorem instantiates its core event. -/
theorem fixedDepthProgram_good_event_of_core_events
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L)
    (hcore : ∀ z : MainSketchSampleTape I, MainSketchGood I (mainSketchFromFiniteSample I z) →
      ∃ E : Set (MainCoreTapeOriginal I), MeasurableSet E ∧
        (mainCoreLawOriginal I).real E ≥ 1-3*I.delta/20 ∧ ∀ c ∈ E,
          ‖I.A*I.B-(mainProgramFromFiniteStateCoreTape kernels I z c).product‖ ≤
            (1+I.theta)*tailSingularValue (I.A*I.B) r) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, (fixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(fixedDepthProgram kernels I g).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  classical
  have hβ : 0 ≤ 3*I.delta/20 := by positivity [I.delta_positive]
  have hEach (z : MainSketchSampleTape I) :
      ∃ E : Set (MainCoreTapeOriginal I), MeasurableSet E ∧
        (mainCoreLawOriginal I).real E ≥ 1-3*I.delta/20 ∧
          (MainSketchGood I (mainSketchFromFiniteSample I z) → ∀ c ∈ E,
            ‖I.A*I.B-(mainProgramFromFiniteStateCoreTape kernels I z c).product‖ ≤
              (1+I.theta)*tailSingularValue (I.A*I.B) r) := by
    by_cases hz : MainSketchGood I (mainSketchFromFiniteSample I z)
    · obtain ⟨E,hEm,hEp,hE⟩ := hcore z hz
      exact ⟨E,hEm,hEp,fun _ => hE⟩
    · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
      · simpa only [probReal_univ] using (show 1-3*I.delta/20 ≤ (1 : ℝ) by linarith)
      · exact fun h => (hz h).elim
  choose E hEm hEp hE using hEach
  have hh := main_random_finite_core_success I E (3*I.delta/20) hβ
    (fun z _ => hEm z) (fun z _ => hEp z)
  refine ⟨_,hh.1,?_,?_⟩
  · have hp := I.delta_positive
    linarith [hh.2]
  · intro g hg
    refine ⟨(fixedDepthProgram kernels I g).eval.rank_le,?_⟩
    rw [fixedDepthProgram_eval_factorization]
    have hz : MainSketchGood I (mainSketchFromFiniteSample I (mainSketchFiniteSample I g)) := by
      simpa only [mainSketchProgram_factorization] using hg.1
    exact hE (mainSketchFiniteSample I g) hz (mainCoreTapeOriginal I g) hg.2

end
end HierarchicalAbsoluteSpectral
