import HierarchicalAbsoluteSpectral.MainCoreProbabilityTape
import HierarchicalAbsoluteSpectral.MainInitializerCorrectnessBase
import HierarchicalAbsoluteSpectral.MainAdaptiveInitial
import HierarchicalAbsoluteSpectral.MainInertiaAdaptiveMain
import HierarchicalAbsoluteSpectral.ProbabilityHistoryConditioning

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def mainCoreInitialGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreInitialHistory I C.pair.dimension) :=
  (Prod.fst ⁻¹' mainInitializerScalarGood kernels I S C hr) ∩
    mainAdaptiveInitialRitzGood kernels I S C hr

theorem mainCoreInitialGood_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreInitialGood kernels I S C hr) :=
  ((mainInitializerScalarGood_measurable kernels I S C hr).preimage measurable_fst).inter
    (mainAdaptiveInitialRitzGood_measurable kernels I S C hr)

theorem MainSketchGood.core_initial_good_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (mainCoreInitialHistoryLaw I C.pair.dimension).real (mainCoreInitialGood kernels I S C hr) ≥
      1-I.singleFailure-(I.queryCap:ℝ)*I.queryFailure := by
  exact (measurable_history_fresh_success (gaussianColumns C.pair.dimension r)
    (mainCoreQueryLaw I C.pair.dimension) (mainInitializerScalarGood kernels I S C hr)
    (mainInitializerScalarGood_measurable kernels I S C hr)
    (mainAdaptiveInitialRitzGood kernels I S C hr)
    (mainAdaptiveInitialRitzGood_measurable kernels I S C hr)
    I.singleFailure ((I.queryCap:ℝ)*I.queryFailure)
    (mul_nonneg (Nat.cast_nonneg _) I.queryFailure_positive.le)
    (mainInitializerScalarGood_probability kernels I S C hr)
    (fun G _ => hg.adaptive_initial_ritz_success kernels I S C hr G)).2

def mainCoreInertiaGoodEvent (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreHistory I C.pair.dimension) :=
  {x | mainAdaptiveInertiaGood kernels I S C hr
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix x.1.1) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix x.1.1))
    (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix x.1.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num)))
    (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix x.1.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num))) x.1.2 x.2}

theorem mainCoreInertiaGoodEvent_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreInertiaGoodEvent kernels I S C hr) := by
  exact mainAdaptiveInertiaGood_measurable kernels I S C hr
    (fun x : MainCoreHistory I C.pair.dimension =>
      mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix x.1.1) I.singleFailure)
    (fun x : MainCoreHistory I C.pair.dimension =>
      mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix x.1.1))
    ((mainInitializerLowerEndpoint_gaussian_measurable (r:=r)
      kernels C.rightGram I.singleFailure).comp measurable_fst.fst)
    ((mainInitializerUpperEndpoint_gaussian_measurable (r:=r)
      kernels C.rightGram).comp measurable_fst.fst)
    (fun x => mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix x.1.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num)))
    (fun x => mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix x.1.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num)))
    (fun x => x.1.2) measurable_fst.snd Prod.snd measurable_snd

theorem mainCoreInertiaGoodEvent_fiber_probability_one
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreInitialHistory I C.pair.dimension) :
    (mainCoreInertiaLaw I C.pair.dimension).real
      (Prod.mk x ⁻¹' mainCoreInertiaGoodEvent kernels I S C hr) = 1 := by
  have hm := (mainCoreInertiaGoodEvent_measurable kernels I S C hr).preimage
    ((measurable_const (a:=x)).prodMk measurable_id)
  have ha := mainAdaptiveInertiaGood_ae kernels I S C hr
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix x.1) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix x.1))
    (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix x.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num)))
    (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix x.1)
      I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num))) x.2
  have heq := (ae_iff_measure_eq hm.nullMeasurableSet).mp ha
  change (mainCoreInertiaLaw I C.pair.dimension)
    (Prod.mk x ⁻¹' mainCoreInertiaGoodEvent kernels I S C hr) =
    (mainCoreInertiaLaw I C.pair.dimension) Set.univ at heq
  rw [Measure.real,heq]
  simp

def mainCoreHistoryGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainCoreHistory I C.pair.dimension) :=
  (Prod.fst ⁻¹' mainCoreInitialGood kernels I S C hr) ∩
    mainCoreInertiaGoodEvent kernels I S C hr

theorem mainCoreHistoryGood_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainCoreHistoryGood kernels I S C hr) :=
  ((mainCoreInitialGood_measurable kernels I S C hr).preimage measurable_fst).inter
    (mainCoreInertiaGoodEvent_measurable kernels I S C hr)

theorem MainSketchGood.core_history_good_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (mainCoreHistoryLaw I C.pair.dimension).real (mainCoreHistoryGood kernels I S C hr) ≥
      1-I.singleFailure-(I.queryCap:ℝ)*I.queryFailure := by
  have hh := measurable_history_fresh_success (mainCoreInitialHistoryLaw I C.pair.dimension)
    (mainCoreInertiaLaw I C.pair.dimension) (mainCoreInitialGood kernels I S C hr)
    (mainCoreInitialGood_measurable kernels I S C hr) (mainCoreInertiaGoodEvent kernels I S C hr)
    (mainCoreInertiaGoodEvent_measurable kernels I S C hr)
    (I.singleFailure+(I.queryCap:ℝ)*I.queryFailure) 0 (by norm_num)
    (by linarith [hg.core_initial_good_probability kernels I S C hr])
    (by intro x _; rw [mainCoreInertiaGoodEvent_fiber_probability_one]; norm_num)
  simpa only [mainCoreHistoryLaw,mainCoreHistoryGood,sub_zero,sub_add_eq_sub_sub] using hh.2

theorem mainCoreProbability_failure_budget (I : FixedProblem n m p r L) :
    2*I.singleFailure+(I.queryCap:ℝ)*I.queryFailure ≤ 3*I.delta/20 := by
  have hq : I.queryFailure*(20*((I.queryCap:ℝ)+1))=I.delta :=
    div_mul_cancel₀ _ (by positivity)
  have hnonneg := I.queryFailure_positive.le
  unfold FixedProblem.singleFailure
  nlinarith

end
end HierarchicalAbsoluteSpectral
