import HierarchicalAbsoluteSpectral.MainCoreProbabilityHistory
import HierarchicalAbsoluteSpectral.MainCoreProbabilitySelected
import HierarchicalAbsoluteSpectral.MainStatementsCoreCorrectness
import HierarchicalAbsoluteSpectral.MainInertiaAdaptiveBridge

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem mainCoreHistoryGood_all_inertia
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreHistory I C.pair.dimension)
    (hx : x ∈ mainCoreHistoryGood kernels I S C hr) :
    MainAllInertiaGood kernels I S C hr
      (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix x.1.1) I.singleFailure)
      (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix x.1.1))
      (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix x.1.1)
        I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num)))
      (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix x.1.1)
        I.singleFailure (by omega) (div_pos I.delta_positive (by norm_num))) x.1.2 x.2 := by
  intro i
  exact mainAdaptiveInertiaGood_query kernels I S C hr _ _ _ _ x.1.2 x.2 hx.2 i

theorem mainCoreHistoryGood_search
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreHistory I C.pair.dimension)
    (hx : x ∈ mainCoreHistoryGood kernels I S C hr) :
    MainCoreSearchGood kernels I S C hr x.1.1 x.1.2 x.2 := by
  refine ⟨?_,mainCoreHistoryGood_all_inertia kernels I S C hr x hx⟩
  rw [← mainAdaptiveInitialRitzGood_fiber kernels I S C hr x.1.1]
  exact hx.1.2

theorem MainSketchGood.core_selected_facts
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (x : MainCoreHistory I C.pair.dimension) (hx : x ∈ mainCoreHistoryGood kernels I S C hr)
    (hpositive : 0 < (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix x.1.1) I.singleFailure).eval.value) :
    let t := mainCoreSelectedThreshold kernels I S C hr x.1
    orderedEigenvalue (mainThresholdView kernels I S C t).val
      (mainThresholdView kernels I S C t).property ⟨r,hr⟩ ≤ 1+I.alpha ∧
      t.val ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
        (tailSingularValue (I.A*I.B) r)^2 :=
  mainCoreSelected_facts kernels I S hg C hr x.1.1 x.1.2 x.2 hx.1.1
    (mainCoreHistoryGood_search kernels I S C hr x hx) hpositive
    (mainCoreSelectedReal_pos kernels I S C hr x.1)

end
end HierarchicalAbsoluteSpectral
