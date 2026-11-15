import HierarchicalAbsoluteSpectral.ThresholdAdaptiveInitial
import HierarchicalAbsoluteSpectral.MainAdaptiveInitialEndpoints
import HierarchicalAbsoluteSpectral.MainStatementsRitzProbability
import HierarchicalAbsoluteSpectral.ProbabilityHistoryConditioning

/-! The joint initializer/adaptive-query event.  The search starts at the
Borel positive extension of its actual computed initial interval.  Every
initializer fiber is the established fixed-endpoint adaptive Ritz event. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator ENNReal
variable {n m p r L : ℕ}
local instance adaptiveInitialMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance adaptiveInitialMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

private theorem mainAdaptiveInitialFailure_pos (I : FixedProblem n m p r L) :
    0 < I.singleFailure := div_pos I.delta_positive (by norm_num)

abbrev MainAdaptiveInitialSource (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :=
  (Fin r → Fin C.pair.dimension → ℝ) ×
    (Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)

def mainAdaptiveInitialThresholdParameter
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainAdaptiveInitialSource I S C) (i : Fin I.queryCap) :
    {t : ℝ // 0 < t} :=
  idealRitzInitialThresholdParameter (k:=C.pair.dimension) (r:=r+1)
    (N:=I.repetitions) (cap:=I.queryCap) kernels (mainThresholdView kernels I S C)
    (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
    (mainRitzAccuracy I) I.nearTolerance
    (fun G => mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix G) I.singleFailure)
    (fun G => mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix G))
    (fun G => mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))
    (fun G => mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I)) x i

theorem mainAdaptiveInitialThresholdParameter_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (i : Fin I.queryCap) :
    Measurable (fun x : MainAdaptiveInitialSource I S C =>
      mainAdaptiveInitialThresholdParameter kernels I S C hr x i) :=
  idealRitzInitialThresholdParameter_measurable (X:=Fin r → Fin C.pair.dimension → ℝ)
    (k:=C.pair.dimension) (r:=r+1) (N:=I.repetitions) (cap:=I.queryCap) kernels
    (mainThresholdView kernels I S C) (mainThresholdView_measurable kernels I S C)
    (mainSourceView kernels I S C) (mainSourceView_measurable kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance
    (fun G => mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix G) I.singleFailure)
    (fun G => mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix G))
    (mainInitializerLowerEndpoint_gaussian_measurable kernels C.rightGram I.singleFailure)
    (mainInitializerUpperEndpoint_gaussian_measurable kernels C.rightGram)
    (fun G => mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))
    (fun G => mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I)) i

theorem mainAdaptiveInitialThresholdParameter_update
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (G : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (i : Fin I.queryCap) (fresh : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ) :
    mainAdaptiveInitialThresholdParameter kernels I S C hr (G,Function.update samples i fresh) i =
      mainAdaptiveInitialThresholdParameter kernels I S C hr (G,samples) i :=
  idealRitzInitialThresholdParameter_update (X:=Fin r → Fin C.pair.dimension → ℝ)
    (k:=C.pair.dimension) (r:=r+1) (N:=I.repetitions) (cap:=I.queryCap) kernels
    (mainThresholdView kernels I S C) (mainSourceView kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance
    (fun G => mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix G) I.singleFailure)
    (fun G => mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix G))
    (fun G => mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))
    (fun G => mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I)) G samples i fresh

/-- On an actual bracket branch, the jointly measurable parameter is
the parameter of the executed search's initial interval. -/
theorem mainAdaptiveInitialThresholdParameter_eq_of_bracket
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (G : Fin r → Fin C.pair.dimension → ℝ)
    (samples : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (lower upper : ℝ)
    (hresult : (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G)
      I.singleFailure).eval.result = .bracket lower upper)
    (hl : 0 < lower/4) (hlu : lower/4 ≤ 4*upper) (i : Fin I.queryCap) :
    mainAdaptiveInitialThresholdParameter kernels I S C hr (G,samples) i =
      idealRitzThresholdParameter kernels (mainThresholdView kernels I S C)
        (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
        (mainRitzAccuracy I) I.nearTolerance (lower/4) (4*upper) hl hlu samples i := by
  have hends := mainInitializerEndpoints_eq_of_bracket kernels C.rightGram
    (columnsMatrix G) I.singleFailure lower upper hresult
  apply Subtype.ext
  simp only [mainAdaptiveInitialThresholdParameter, idealRitzInitialThresholdParameter,
    idealRitzThresholdParameter, hends.1, hends.2]

def mainAdaptiveInitialRitzGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : Set (MainAdaptiveInitialSource I S C) :=
  ⋂ i : Fin I.queryCap, {x |
    (mainAdaptiveInitialThresholdParameter kernels I S C hr x i,x.2 i) ∈
      mainRepeatedRitzBad kernels I S C hr}ᶜ

theorem mainAdaptiveInitialRitzGood_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    MeasurableSet (mainAdaptiveInitialRitzGood kernels I S C hr) := by
  unfold mainAdaptiveInitialRitzGood
  apply MeasurableSet.iInter
  intro i
  exact ((mainRepeatedRitzBad_measurable kernels I S C hr).preimage
    ((mainAdaptiveInitialThresholdParameter_measurable kernels I S C hr i).prodMk
      ((measurable_pi_apply i).comp measurable_snd))).compl

theorem mainAdaptiveInitialRitzGood_fiber
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (G : Fin r → Fin C.pair.dimension → ℝ) :
    {samples | (G,samples) ∈ mainAdaptiveInitialRitzGood kernels I S C hr} =
      mainAdaptiveRitzGood kernels I S C hr
        (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix G) I.singleFailure)
        (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix G))
        (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix G)
          I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))
        (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix G)
          I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I)) := by
  ext samples
  simp only [Set.mem_setOf_eq, mainAdaptiveInitialRitzGood, mainAdaptiveRitzGood,
    Set.mem_iInter, Set.mem_compl_iff, mainAdaptiveInitialThresholdParameter,
    idealRitzInitialThresholdParameter]

/-- The adaptive failure budget is uniform over all initializer draws,
including the draws on which the actual initializer takes its exact branch. -/
theorem MainSketchGood.adaptive_initial_ritz_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (Measure.pi (fun _ : Fin I.queryCap =>
      repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions)).real
        {samples | (G,samples) ∈ mainAdaptiveInitialRitzGood kernels I S C hr} ≥
          1-(I.queryCap:ℝ)*I.queryFailure := by
  rw [mainAdaptiveInitialRitzGood_fiber]
  exact (hg.adaptive_ritz_success kernels I S C hr
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix G) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix G))
    (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))
    (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix G)
      I.singleFailure (by omega) (mainAdaptiveInitialFailure_pos I))).2

/-- Integrating the uniform initializer fibers preserves the adaptive
failure budget for any independent initializer law. -/
theorem MainSketchGood.adaptive_initial_ritz_prod_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (μ : Measure (Fin r → Fin C.pair.dimension → ℝ)) [IsProbabilityMeasure μ] :
    (μ.prod (Measure.pi (fun _ : Fin I.queryCap =>
      repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions))).real
        (mainAdaptiveInitialRitzGood kernels I S C hr) ≥ 1-(I.queryCap:ℝ)*I.queryFailure := by
  have hh := measurable_history_fresh_success μ
    (Measure.pi (fun _ : Fin I.queryCap =>
      repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions))
    Set.univ MeasurableSet.univ (mainAdaptiveInitialRitzGood kernels I S C hr)
    (mainAdaptiveInitialRitzGood_measurable kernels I S C hr) 0
    ((I.queryCap:ℝ)*I.queryFailure)
    (mul_nonneg (Nat.cast_nonneg _) I.queryFailure_positive.le)
    (by simp) (fun G _ => hg.adaptive_initial_ritz_success kernels I S C hr G)
  simpa only [Set.preimage_univ, Set.univ_inter, sub_zero] using hh.2

end
end HierarchicalAbsoluteSpectral
