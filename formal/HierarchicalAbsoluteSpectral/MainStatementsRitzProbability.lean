import HierarchicalAbsoluteSpectral.MainStatementsQueryViews

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator ENNReal
variable {n m p r L : ℕ}
local instance mainRitzMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance mainRitzMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

def mainRepeatedRitzBad (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    Set ({t : ℝ // 0 < t} × (Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)) :=
  {x | ((mainThresholdView kernels I S C x.1,mainSourceView kernels I S C x.1),x.2) ∈
    ritzRepeatedFailureSet kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.repetitions}

theorem mainRepeatedRitzBad_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : MeasurableSet (mainRepeatedRitzBad kernels I S C hr) := by
  apply (ritzRepeatedFailureSet_measurable kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩
    (mainRitzAccuracy I) I.repetitions).preimage
  exact (((mainThresholdView_measurable kernels I S C).comp measurable_fst).prodMk
    ((mainSourceView_measurable kernels I S C).comp measurable_fst)).prodMk measurable_snd

theorem MainSketchGood.repeated_ritz_bad_fiber (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t}) :
    repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions
      {G | (t,G) ∈ mainRepeatedRitzBad kernels I S C hr} ≤ ENNReal.ofReal I.queryFailure := by
  let base := mainBaseAt kernels I S C t
  let T := mainThresholdOperator I S C t.val base
  let source := mainSourceFactor I S C t.val base
  let Sinv := (mainRefinedFactor I S C t.val base)⁻¹*base.inverseFactor
  let a := (1+hierarchyUpper L/(8*I.accuracy 0))⁻¹
  let b := 1+hierarchyUpper 0/(8*I.accuracy L)
  have hT : T.PosSemidef := (hg.actual_threshold_bounds kernels I S C t.val t.property).1
  have hc := hg.actual_source_condition kernels I S C t.val t.property
  have hstop : 10*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) (1/2)/(mainRitzAccuracy I) ≤
      strongFilterDenominator (mainRitzAccuracy I/100) (mainKrylovDegree I S C hr) :=
    krylovDegree_stops _ _ _ _ (by omega) (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
      (mainRitzAccuracy_positive I) (mainRitzAccuracy_le_one I)
  have hh := ritzRepeatedFailureSet_fiber_probability kernels T hT
    (fun width => mainThresholdAction kernels I S C t.val base width)
    source Sinv hc.1 ⟨r,hr⟩ a b (mainConditionBound I) (1/2) (mainRitzAccuracy I)
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
    (by norm_num) (by norm_num) (mainRitzAccuracy_positive I) (mainRitzAccuracy_le_one I)
    (mainKrylovDegree I S C hr) hstop I.repetitions
  have hhalf : (1/2:ℝ)^I.repetitions ≤ I.queryFailure :=
    repetition_halving_cap I.queryFailure I.queryFailure_positive (1/2) (by norm_num) (by norm_num)
  have hrb : (repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions).real
      {G | (t,G) ∈ mainRepeatedRitzBad kernels I S C hr} ≤ I.queryFailure := by
    exact hh.trans hhalf
  have hENN := ENNReal.ofReal_le_ofReal hrb
  have hne : repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions
      {G | (t,G) ∈ mainRepeatedRitzBad kernels I S C hr} ≠ ⊤ := by finiteness
  simpa only [measureReal_def,ENNReal.ofReal_toReal hne] using hENN

def mainAdaptiveRitzGood (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    Set (Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ) :=
  ⋂ i : Fin I.queryCap, {samples |
    (idealRitzThresholdParameter kernels (mainThresholdView kernels I S C) (mainSourceView kernels I S C)
      (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance l u hl hlu samples i,
      samples i) ∈ mainRepeatedRitzBad kernels I S C hr}ᶜ

theorem MainSketchGood.adaptive_ritz_success (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    MeasurableSet (mainAdaptiveRitzGood kernels I S C hr l u hl hlu) ∧
      (Measure.pi (fun _ : Fin I.queryCap => repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions)).real
        (mainAdaptiveRitzGood kernels I S C hr l u hl hlu) ≥ 1-(I.queryCap:ℝ)*I.queryFailure := by
  let parameter := idealRitzThresholdParameter (r:=r+1) (N:=I.repetitions) (cap:=I.queryCap)
    kernels (mainThresholdView kernels I S C)
    (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
    (mainRitzAccuracy I) I.nearTolerance l u hl hlu
  have hp : ∀ i : Fin I.queryCap, Measurable (fun samples => parameter samples i) := fun i =>
    idealRitzThresholdParameter_measurable kernels _ (mainThresholdView_measurable kernels I S C)
      _ (mainSourceView_measurable kernels I S C) _ _ _ _ _ _ hl hlu i
  have hi : ∀ samples i fresh, parameter (Function.update samples i fresh) i=parameter samples i :=
    idealRitzThresholdParameter_update kernels _ _ _ _ _ _ _ _ hl hlu
  have hm : MeasurableSet (mainAdaptiveRitzGood kernels I S C hr l u hl hlu) := by
    unfold mainAdaptiveRitzGood
    apply MeasurableSet.iInter
    intro i
    exact ((mainRepeatedRitzBad_measurable kernels I S C hr).preimage
      ((hp i).prodMk (measurable_pi_apply i))).compl
  have hb := adaptive_finite_failure_probability
    (repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions) I.queryCap parameter hp hi
    (mainRepeatedRitzBad kernels I S C hr) (mainRepeatedRitzBad_measurable kernels I S C hr)
    I.queryFailure I.queryFailure_positive.le (hg.repeated_ritz_bad_fiber kernels I S C hr)
  exact ⟨hm,hb.2⟩

end
end HierarchicalAbsoluteSpectral
