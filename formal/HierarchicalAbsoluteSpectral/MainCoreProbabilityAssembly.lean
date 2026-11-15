import HierarchicalAbsoluteSpectral.MainCoreProbabilityFacts
import HierarchicalAbsoluteSpectral.MainStrongProbabilityJoint

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] mainStrongThresholdProgram mainThresholdOperator

def mainCoreStrongGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreTapeGrouped I C.pair.dimension) :=
  {z | (gaussianInitializerProgram kernels C.rightGram (columnsMatrix z.1.1.1) I.singleFailure).eval.value ≤ 0 ∨
    ‖I.A*I.B-(mainStrongThresholdProgram kernels I S C (by omega)
      (mainCoreSelectedThreshold kernels I S C hr z.1.1) z.2).eval.product‖ ≤
      (1+I.theta)*tailSingularValue (I.A*I.B) r}

theorem mainCoreStrongGood_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreStrongGood kernels I S C hr) := by
  have hv := (gaussianInitializerProgram_value_gaussian_measurable (r:=r)
    kernels C.rightGram I.singleFailure).comp
    (measurable_fst.fst.fst : Measurable (fun z : MainCoreTapeGrouped I C.pair.dimension => z.1.1.1))
  have ht := (mainCoreSelectedThreshold_measurable kernels I S C hr).comp
    (measurable_fst.fst : Measurable (fun z : MainCoreTapeGrouped I C.pair.dimension => z.1.1))
  have hs := (mainStrongThresholdProgram_error_joint_measurable kernels I S C (by omega)).preimage
    (ht.prodMk measurable_snd)
  exact (measurableSet_le hv measurable_const).union hs

theorem MainSketchGood.core_strong_good_fiber_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (x : MainCoreHistory I C.pair.dimension) (hx : x ∈ mainCoreHistoryGood kernels I S C hr) :
    (gaussianColumns C.pair.dimension r).real
      (Prod.mk x ⁻¹' mainCoreStrongGood kernels I S C hr) ≥ 1-I.singleFailure := by
  by_cases htau : (gaussianInitializerProgram kernels C.rightGram (columnsMatrix x.1.1) I.singleFailure).eval.value ≤ 0
  · have he : Prod.mk x ⁻¹' mainCoreStrongGood kernels I S C hr = Set.univ := by
      ext G
      simp only [mainCoreStrongGood,Set.mem_preimage,Set.mem_setOf_eq,htau,true_or,Set.mem_univ]
    rw [he,probReal_univ]
    linarith [I.singleFailure_positive]
  · have hs := hg.core_selected_facts kernels I S C hr x hx (lt_of_not_ge htau)
    have hp := mainStrongThresholdProgram_error_probability kernels I S hg C hr (by omega)
      (mainCoreSelectedThreshold kernels I S C hr x.1) hs.1 hs.2
    exact hp.trans (measureReal_mono (fun G hG => Or.inr hG))

def mainCoreGroupedGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreTapeGrouped I C.pair.dimension) :=
  (Prod.fst ⁻¹' mainCoreHistoryGood kernels I S C hr) ∩ mainCoreStrongGood kernels I S C hr

theorem mainCoreGroupedGood_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreGroupedGood kernels I S C hr) :=
  ((mainCoreHistoryGood_measurable kernels I S C hr).preimage measurable_fst).inter
    (mainCoreStrongGood_measurable kernels I S C hr)

theorem MainSketchGood.core_grouped_good_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (mainCoreLawGrouped I C.pair.dimension).real (mainCoreGroupedGood kernels I S C hr) ≥
      1-3*I.delta/20 := by
  have hh := measurable_history_fresh_success (mainCoreHistoryLaw I C.pair.dimension)
    (gaussianColumns C.pair.dimension r) (mainCoreHistoryGood kernels I S C hr)
    (mainCoreHistoryGood_measurable kernels I S C hr) (mainCoreStrongGood kernels I S C hr)
    (mainCoreStrongGood_measurable kernels I S C hr)
    (I.singleFailure+(I.queryCap:ℝ)*I.queryFailure) I.singleFailure I.singleFailure_positive.le
    (by linarith [hg.core_history_good_probability kernels I S C hr])
    (fun x hx => hg.core_strong_good_fiber_probability kernels I S C hr x hx)
  have hb := mainCoreProbability_failure_budget I
  change ((mainCoreHistoryLaw I C.pair.dimension).prod (gaussianColumns C.pair.dimension r)).real
    (Prod.fst ⁻¹' mainCoreHistoryGood kernels I S C hr ∩ mainCoreStrongGood kernels I S C hr) ≥ _
  linarith [hh.2]

def mainCoreOriginalGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreTapeOriginal I) :=
  mainCoreOriginalToGrouped I (mainSupport_dimension_le S C) ⁻¹' mainCoreGroupedGood kernels I S C hr

theorem mainCoreOriginalGood_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreOriginalGood kernels I S C hr) :=
  (mainCoreGroupedGood_measurable kernels I S C hr).preimage
    (mainCoreOriginalToGrouped_measurePreserving I (mainSupport_dimension_le S C)).measurable

theorem MainSketchGood.core_original_good_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (mainCoreLawOriginal I).real (mainCoreOriginalGood kernels I S C hr) ≥ 1-3*I.delta/20 := by
  rw [mainCoreOriginalGood,
    (mainCoreOriginalToGrouped_measurePreserving I (mainSupport_dimension_le S C)).measureReal_preimage
      (mainCoreGroupedGood_measurable kernels I S C hr).nullMeasurableSet]
  exact hg.core_grouped_good_probability kernels I S C hr

theorem MainSketchGood.core_original_good_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (c : MainCoreTapeOriginal I)
    (hc : c ∈ mainCoreOriginalGood kernels I S C hr) :
    ‖I.A*I.B-(mainCoreProgramFromOriginalTape kernels I S C c).eval.product‖ ≤
      (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  let z := mainCoreOriginalToGrouped I (mainSupport_dimension_le S C) c
  have hz : z ∈ mainCoreGroupedGood kernels I S C hr := hc
  apply mainCoreProgram_error_of_events kernels I S hg C hr (mainCoreTapeExtend I c)
  · exact hz.1.1.1
  · exact mainCoreHistoryGood_search kernels I S C hr z.1 hz.1
  · intro hpositive
    rcases hz.2 with hzero | hstrong
    · exact False.elim (not_le_of_gt hpositive hzero)
    · exact hstrong

/-- Fixed good stored sketches yield a measurable sufficient event on the
original remaining core tape, with the complete three-stage failure budget. -/
theorem mainCoreProgramFromOriginalTape_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) :
    ∃ E : Set (MainCoreTapeOriginal I), MeasurableSet E ∧
      (mainCoreLawOriginal I).real E ≥ 1-3*I.delta/20 ∧ ∀ c ∈ E,
        ‖I.A*I.B-(mainCoreProgramFromOriginalTape kernels I S C c).eval.product‖ ≤
          (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  by_cases hrank : C.pair.dimension ≤ r
  · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
    · rw [probReal_univ]
      linarith [I.delta_positive]
    · intro c _
      rw [mainCoreProgramFromOriginalTape,
        hg.mainCoreProgram_exact_of_small_dimension kernels I S C (mainCoreTapeExtend I c) hrank,
        sub_self,norm_zero]
      exact mul_nonneg (by linarith [I.theta_positive]) (tailSingularValue_nonneg _ _)
  · have hr : r < C.pair.dimension := Nat.lt_of_not_ge hrank
    exact ⟨mainCoreOriginalGood kernels I S C hr,
      mainCoreOriginalGood_measurable kernels I S C hr,
      hg.core_original_good_probability kernels I S C hr,
      fun c hc => hg.core_original_good_error kernels I S C hr c hc⟩

end
end HierarchicalAbsoluteSpectral
