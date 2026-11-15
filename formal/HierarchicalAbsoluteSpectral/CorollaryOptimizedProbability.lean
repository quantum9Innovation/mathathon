import HierarchicalAbsoluteSpectral.CorollaryOptimizedPrograms
import HierarchicalAbsoluteSpectral.MainStatementsProbability

/-! Both actual comparator programs have the original relative spectral
guarantee.  Exact stored factors make the Gram comparator's sketch event
deterministic; the remaining probability is proved on its actual tape. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] mainCoreProgram fixedDepthProgram

theorem comparator_coreTape_measurePreserving (I : FixedProblem n m p r L) :
    MeasurePreserving (mainCoreTapeOriginal I) (mainRandomLaw I) (mainCoreLawOriginal I) := by
  letI : IsProbabilityMeasure ((mainRandomLaw I).map (mainSketchFiniteSample I)) :=
    Measure.isProbabilityMeasure_map (mainSketchFiniteSample_measurable I).aemeasurable
  exact (measurePreserving_snd
    (μ := (mainRandomLaw I).map (mainSketchFiniteSample I)) (ν := mainCoreLawOriginal I)).comp
      (mainSketchFiniteSample_coreTape_measurePreserving I)

theorem comparator_core_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (hgood : MainSketchGood I S) (C : MainSupportData S) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-3*I.delta/20 ∧
      ∀ g ∈ E, ‖I.A*I.B-(mainCoreProgram kernels I S C g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  obtain ⟨E,hEm,hEp,hE⟩ := mainCoreProgramFromOriginalTape_good_event kernels I S hgood C
  have hmp := comparator_coreTape_measurePreserving I
  refine ⟨mainCoreTapeOriginal I ⁻¹' E,hEm.preimage hmp.measurable,?_,?_⟩
  · rw [hmp.measureReal_preimage hEm.nullMeasurableSet]
    exact hEp
  · intro g hg
    have hh := hE (mainCoreTapeOriginal I g) hg
    have he : mainCoreProgram kernels I S C g=
        mainCoreProgramFromOriginalTape kernels I S C (mainCoreTapeOriginal I g) :=
      mainCoreProgram_factorization kernels I S C g
    rw [he]
    exact hh

theorem constantDistortionComparatorProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r 1) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖I.A*I.B-(constantDistortionComparatorProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  simpa only [constantDistortionComparatorProgram_eval] using fixedDepthProgram_error_probability kernels I

theorem exactGramComparatorProgram_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, (exactGramComparatorProgram kernels I g).eval.width ≤ r ∧
        ‖I.A*I.B-(exactGramComparatorProgram kernels I g).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  let S := exactComparatorSketches I.A I.B L
  let C : MainSupportData S := (coarseSupportProgram kernels I.A I.Bᵀ).eval
  obtain ⟨E,hEm,hEp,hE⟩ := comparator_core_good_event kernels I S (exactComparatorSketches_good I) C
  refine ⟨E,hEm,by linarith [I.delta_positive],?_⟩
  intro g hg
  refine ⟨(exactGramComparatorProgram kernels I g).eval.width_le,?_⟩
  rw [exactGramComparatorProgram_eval]
  exact hE g hg

theorem exactGramComparatorProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖I.A*I.B-(exactGramComparatorProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := exactGramComparatorProgram_good_event kernels I
  exact hEp.trans (measureReal_mono (fun g hg => (hE g hg).2))

end
end HierarchicalAbsoluteSpectral
