import HierarchicalAbsoluteSpectral.MainInertiaAdaptiveMain
import HierarchicalAbsoluteSpectral.MainStatementsQueryCorrectness

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

/-- The probability-one adaptive event supplies exactly the premise of
the main query's existing exact-test correctness theorem, at every ideal
history threshold. -/
theorem mainAdaptiveInertiaGood_query
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : MainAdaptiveQueryTape I S C)
    (g : AdaptiveInertiaTape C.pair.dimension I.queryCap I.repetitions)
    (hg : mainAdaptiveInertiaGood kernels I S C hr l u hl hlu samples g)
    (i : Fin I.queryCap) :
    MainQueryInertiaGood kernels I S C hr
      (idealRitzThresholdParameter kernels (mainThresholdView kernels I S C)
        (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
        (mainRitzAccuracy I) I.nearTolerance l u hl hlu samples i)
      (samples i) (g i) := by
  intro trial
  constructor
  · simpa only [mainTrialRitzMatrix,idealRitzAdaptiveMatrix,adaptiveInertiaShift,ite_true]
      using hg i trial 0
  · simpa [mainTrialRitzMatrix,idealRitzAdaptiveMatrix,adaptiveInertiaShift]
      using hg i trial 1

end
end HierarchicalAbsoluteSpectral
