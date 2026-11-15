import HierarchicalAbsoluteSpectral.MainInertiaAdaptive

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

variable {k b N cap : ℕ}

/-- The Borel sufficient event implies successful execution of both
literal shifted tests in every full-size Gaussian Krylov trial. -/
theorem idealRitzAdaptiveInertiaGood_tests_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin b → Fin k → ℝ)
    (g : AdaptiveInertiaTape k cap N)
    (hg : idealRitzAdaptiveInertiaGood kernels T S q j ε searchAccuracy l u hl hlu samples g)
    (i : Fin cap) (trial : Fin N) :
    let t := idealRitzThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu samples i
    ∀ (actions : ∀ w, MatrixAction (T t).val w) (source : MatrixAction (S t)ᵀ b),
      ∃ out, (gaussianKrylovRitzTestsProgram kernels (T t).val (T t).property actions
        q (S t) source (samples i trial) j ε (g i trial)).eval = some out := by
  dsimp only
  intro actions source
  apply gaussianKrylovRitzTestsProgram_success_of_polynomial_events
  · exact jointInertiaGood_polynomial_event _ _ (by
      simpa only [idealRitzAdaptiveMatrix,adaptiveInertiaShift,ite_true] using hg i trial 0)
  · exact jointInertiaGood_polynomial_event _ _ (by
      simpa [idealRitzAdaptiveMatrix,adaptiveInertiaShift] using hg i trial 1)

variable {n m p r L : ℕ}

abbrev MainAdaptiveQueryTape (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :=
  Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ

def mainAdaptiveInertiaGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : MainAdaptiveQueryTape I S C)
    (g : AdaptiveInertiaTape C.pair.dimension I.queryCap I.repetitions) : Prop :=
  idealRitzAdaptiveInertiaGood kernels (mainThresholdView kernels I S C)
    (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
    (mainRitzAccuracy I) I.nearTolerance l u hl hlu samples g

theorem mainAdaptiveInertiaGood_measurable
    {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → MainAdaptiveQueryTape I S C) (hsamples : Measurable samples)
    (g : X → AdaptiveInertiaTape C.pair.dimension I.queryCap I.repetitions)
    (hg : Measurable g) :
    MeasurableSet {x | mainAdaptiveInertiaGood kernels I S C hr
      (l x) (u x) (hlpos x) (hlu x) (samples x) (g x)} :=
  idealRitzAdaptiveInertiaGood_measurable kernels
    (mainThresholdView kernels I S C) (mainThresholdView_measurable kernels I S C)
    (mainSourceView kernels I S C) (mainSourceView_measurable kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance
    l u hl hu hlpos hlu samples hsamples g hg

theorem mainAdaptiveInertiaGood_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : MainAdaptiveQueryTape I S C) :
    ∀ᵐ g ∂adaptiveInertiaLaw C.pair.dimension I.queryCap I.repetitions,
      mainAdaptiveInertiaGood kernels I S C hr l u hl hlu samples g :=
  idealRitzAdaptiveInertiaGood_ae kernels (mainThresholdView kernels I S C)
    (mainSourceView kernels I S C) (mainKrylovDegree I S C hr) ⟨r,hr⟩
    (mainRitzAccuracy I) I.nearTolerance l u hl hlu samples

theorem mainAdaptiveInertiaGood_prod_probability_one
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → MainAdaptiveQueryTape I S C) (hsamples : Measurable samples) :
    (μ.prod (adaptiveInertiaLaw C.pair.dimension I.queryCap I.repetitions)).real
      {z | mainAdaptiveInertiaGood kernels I S C hr
        (l z.1) (u z.1) (hlpos z.1) (hlu z.1) (samples z.1) z.2} = 1 :=
  idealRitzAdaptiveInertiaGood_prod_probability_one μ kernels
    (mainThresholdView kernels I S C) (mainThresholdView_measurable kernels I S C)
    (mainSourceView kernels I S C) (mainSourceView_measurable kernels I S C)
    (mainKrylovDegree I S C hr) ⟨r,hr⟩ (mainRitzAccuracy I) I.nearTolerance
    l u hl hu hlpos hlu samples hsamples

/-- The natural Borel space of valid initial endpoints. -/
abbrev AdaptiveInitialBracket := {lu : ℝ × ℝ // 0 < lu.1 ∧ lu.1 ≤ lu.2}
attribute [local irreducible] mainAdaptiveInertiaGood

theorem mainAdaptiveInertiaGood_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    MeasurableSet {z : (AdaptiveInitialBracket × MainAdaptiveQueryTape I S C) ×
        AdaptiveInertiaTape C.pair.dimension I.queryCap I.repetitions |
      mainAdaptiveInertiaGood kernels I S C hr z.1.1.val.1 z.1.1.val.2
        z.1.1.property.1 z.1.1.property.2 z.1.2 z.2} := by
  exact mainAdaptiveInertiaGood_measurable
    (X := (AdaptiveInitialBracket × MainAdaptiveQueryTape I S C) ×
      AdaptiveInertiaTape C.pair.dimension I.queryCap I.repetitions)
    kernels I S C hr
    (fun z => z.1.1.val.1) (fun z => z.1.1.val.2)
    measurable_fst.fst.subtype_coe.fst measurable_fst.fst.subtype_coe.snd
    (fun z => z.1.1.property.1) (fun z => z.1.1.property.2)
    (fun z => z.1.2) measurable_fst.snd Prod.snd measurable_snd

theorem mainAdaptiveInertiaGood_joint_probability_one
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension)
    (μ : Measure (AdaptiveInitialBracket × MainAdaptiveQueryTape I S C))
    [IsProbabilityMeasure μ] :
    (μ.prod (adaptiveInertiaLaw C.pair.dimension I.queryCap I.repetitions)).real
      {z | mainAdaptiveInertiaGood kernels I S C hr z.1.1.val.1 z.1.1.val.2
        z.1.1.property.1 z.1.1.property.2 z.1.2 z.2} = 1 := by
  exact mainAdaptiveInertiaGood_prod_probability_one
    (X := AdaptiveInitialBracket × MainAdaptiveQueryTape I S C)
    μ kernels I S C hr
    (fun x => x.1.val.1) (fun x => x.1.val.2)
    measurable_fst.subtype_coe.fst measurable_fst.subtype_coe.snd
    (fun x => x.1.property.1) (fun x => x.1.property.2)
    Prod.snd measurable_snd

end
end HierarchicalAbsoluteSpectral
