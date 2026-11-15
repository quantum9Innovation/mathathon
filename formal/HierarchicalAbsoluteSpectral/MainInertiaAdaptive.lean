import HierarchicalAbsoluteSpectral.MainStatementsQueryViews
import HierarchicalAbsoluteSpectral.ProbabilityJointInertiaProgram

/-! The exact inertia event along the ideal query history.  The history uses
only the initial endpoints and the query samples.  All inertia arrays remain
fresh after conditioning on those data, including at rank-deficient Ritz
matrices. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k b N cap : ℕ}

local instance inertiaAdaptiveMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance inertiaAdaptiveMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

abbrev AdaptiveInertiaTape (k cap N : ℕ) :=
  Fin cap → Fin N → Fin 2 → Fin (k*k) → ℝ

def adaptiveInertiaLaw (k cap N : ℕ) : Measure (AdaptiveInertiaTape k cap N) :=
  Measure.pi (fun _ : Fin cap => Measure.pi (fun _ : Fin N =>
    Measure.pi (fun _ : Fin 2 => gaussianVector (k*k))))

instance adaptiveInertiaLaw_isProbability (k cap N : ℕ) :
    IsProbabilityMeasure (adaptiveInertiaLaw k cap N) := by
  unfold adaptiveInertiaLaw
  infer_instance

/-- The ideal parameter is Borel even when the initial endpoints vary with
the same external data as the query samples. -/
theorem idealRitzThresholdParameter_measurable_with_endpoints
    {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin b → Fin k → ℝ)
    (hsamples : Measurable samples) (i : Fin cap) :
    Measurable (fun x => idealRitzThresholdParameter kernels T S q j ε searchAccuracy
      (l x) (u x) (hlpos x) (hlu x) (samples x) i) := by
  have hhistory : ∀ (n : ℕ) (hn : n ≤ cap), Measurable (fun x =>
      thresholdQueryHistory (idealRitzDecisions kernels T S q j ε (samples x))
        searchAccuracy (l x) (u x) n hn) := by
    intro n
    induction n with
    | zero => intro _; exact hl.prodMk (hu.prodMk measurable_const)
    | succ n ih =>
      intro hn
      let number : Fin cap := ⟨n, by omega⟩
      let state := fun x =>
        thresholdQueryHistory (idealRitzDecisions kernels T S q j ε (samples x))
          searchAccuracy (l x) (u x) n (by omega)
      have hs : Measurable state := ih (by omega)
      have hm : Measurable (fun x => ((state x).1+(state x).2.1)/2) :=
        (hs.fst.add hs.snd.fst).div_const 2
      have hpos : ∀ x, 0 < ((state x).1+(state x).2.1)/2 := fun x =>
        thresholdQueryHistory_midpoint_positive _ searchAccuracy (l x) (u x)
          (hlpos x) (hlu x) number
      let time := fun x =>
        (⟨((state x).1+(state x).2.1)/2,hpos x⟩ : {t : ℝ // 0 < t})
      have htime : Measurable time := hm.subtype_mk
      have hp : Measurable (fun x => (T (time x),S (time x))) :=
        (hT.comp htime).prodMk (hS.comp htime)
      have hv : ∀ trial : Fin N, Measurable (fun x =>
          gaussianRitzObservable kernels q j
            ((T (time x),S (time x)),samples x number trial)) := by
        intro trial
        exact (gaussianRitzObservable_measurable kernels q j).comp
          (hp.prodMk ((measurable_pi_apply trial).comp
            ((measurable_pi_apply number).comp hsamples)))
      have ha : Measurable (fun x =>
          idealRitzDecisions kernels T S q j ε (samples x) number
            (((state x).1+(state x).2.1)/2)) := by
        convert thresholdDecision_measurable _ hv ε using 1
        funext x
        simp only [idealRitzDecisions,positiveRitzDecision,dif_pos (hpos x)]
        rfl
      exact thresholdQueryStep_measurable_of_answer
        (fun x => idealRitzDecisions kernels T S q j ε (samples x))
        searchAccuracy number state hs ha
  have hs := hhistory i.val i.isLt.le
  exact ((hs.fst.add hs.snd.fst).div_const 2).subtype_mk

def idealRitzAdaptiveMatrix
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin b → Fin k → ℝ)
    (i : Fin cap) (trial : Fin N) : Core k :=
  let t := idealRitzThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu samples i
  krylovRitzFixedMatrix kernels (T t).val q ((S t)ᵀ*columnsMatrix (samples i trial))

def adaptiveInertiaShift (ε : ℝ) (test : Fin 2) : ℝ :=
  if test = 0 then 1 else 1-2*ε

/-- Both exact tests on the actual full-size Ritz matrix, at every ideal
query and every trial.  The matrix never depends on an inertia coordinate. -/
def idealRitzAdaptiveInertiaGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin b → Fin k → ℝ)
    (g : AdaptiveInertiaTape k cap N) : Prop :=
  ∀ (i : Fin cap) (trial : Fin N) (test : Fin 2),
    jointInertiaGood
      (idealRitzAdaptiveMatrix kernels T S q j ε searchAccuracy l u hl hlu samples i trial-
        adaptiveInertiaShift ε test • (1 : Core k)) (g i trial test)

theorem idealRitzAdaptiveMatrix_measurable
    {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin b → Fin k → ℝ)
    (hsamples : Measurable samples) (i : Fin cap) (trial : Fin N) :
    Measurable (fun x => idealRitzAdaptiveMatrix kernels T S q j ε searchAccuracy
      (l x) (u x) (hlpos x) (hlu x) (samples x) i trial) := by
  let time := fun x => idealRitzThresholdParameter kernels T S q j ε searchAccuracy
    (l x) (u x) (hlpos x) (hlu x) (samples x) i
  have ht : Measurable time := idealRitzThresholdParameter_measurable_with_endpoints
    kernels T hT S hS q j ε searchAccuracy l u hl hu hlpos hlu samples hsamples i
  have hcols : Measurable (fun x => columnsMatrix (samples x i trial)) :=
    columnsMatrix_continuous.measurable.comp
      ((measurable_pi_apply trial).comp ((measurable_pi_apply i).comp hsamples))
  have hsource : Measurable (fun x => (S (time x))ᵀ*columnsMatrix (samples x i trial)) :=
    (continuous_fst.matrix_transpose.matrix_mul continuous_snd).measurable.comp
      ((hS.comp ht).prodMk hcols)
  exact (krylovRitzFixedMatrix_measurable kernels q).comp
    ((hT.comp ht).subtype_coe.prodMk hsource)

theorem idealRitzAdaptiveInertiaGood_measurable
    {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin b → Fin k → ℝ)
    (hsamples : Measurable samples) (g : X → AdaptiveInertiaTape k cap N)
    (hg : Measurable g) :
    MeasurableSet {x | idealRitzAdaptiveInertiaGood kernels T S q j ε searchAccuracy
      (l x) (u x) (hlpos x) (hlu x) (samples x) (g x)} := by
  simp only [idealRitzAdaptiveInertiaGood,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro trial
  apply MeasurableSet.iInter
  intro test
  exact jointInertiaGood_measurable_comp _ _
    ((idealRitzAdaptiveMatrix_measurable kernels T hT S hS q j ε searchAccuracy
      l u hl hu hlpos hlu samples hsamples i trial).sub measurable_const)
    ((measurable_pi_apply test).comp ((measurable_pi_apply trial).comp
      ((measurable_pi_apply i).comp hg)))

/-- After fixing all initial data and all query samples, the complete
inertia event has probability one. -/
theorem idealRitzAdaptiveInertiaGood_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin b → Fin k → ℝ) :
    ∀ᵐ g ∂adaptiveInertiaLaw k cap N,
      idealRitzAdaptiveInertiaGood kernels T S q j ε searchAccuracy l u hl hlu samples g := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro trial
  apply ae_all_iff.mpr
  intro test
  have heval :=
    (measurePreserving_eval (fun _ : Fin 2 => gaussianVector (k*k)) test).comp
      ((measurePreserving_eval
        (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => gaussianVector (k*k))) trial).comp
        (measurePreserving_eval
          (fun _ : Fin cap => Measure.pi (fun _ : Fin N =>
            Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)))) i))
  exact heval.quasiMeasurePreserving.ae (jointInertiaGood_ae _)

/-- Any law on the initial endpoints and query samples can be combined
with the independent inertia law. -/
theorem idealRitzAdaptiveInertiaGood_prod_ae
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin b → Fin k → ℝ)
    (hsamples : Measurable samples) :
    ∀ᵐ z ∂μ.prod (adaptiveInertiaLaw k cap N),
      idealRitzAdaptiveInertiaGood kernels T S q j ε searchAccuracy
        (l z.1) (u z.1) (hlpos z.1) (hlu z.1) (samples z.1) z.2 := by
  have hm := idealRitzAdaptiveInertiaGood_measurable kernels T hT S hS q j ε searchAccuracy
    (fun z : X × AdaptiveInertiaTape k cap N => l z.1)
    (fun z : X × AdaptiveInertiaTape k cap N => u z.1)
    (hl.comp measurable_fst) (hu.comp measurable_fst)
    (fun z => hlpos z.1) (fun z => hlu z.1)
    (fun z => samples z.1) (hsamples.comp measurable_fst) Prod.snd measurable_snd
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact Filter.Eventually.of_forall (fun x => idealRitzAdaptiveInertiaGood_ae
    kernels T S q j ε searchAccuracy (l x) (u x) (hlpos x) (hlu x) (samples x))

theorem idealRitzAdaptiveInertiaGood_prod_probability_one
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (hlpos : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin b → Fin k → ℝ)
    (hsamples : Measurable samples) :
    (μ.prod (adaptiveInertiaLaw k cap N)).real
      {z | idealRitzAdaptiveInertiaGood kernels T S q j ε searchAccuracy
        (l z.1) (u z.1) (hlpos z.1) (hlu z.1) (samples z.1) z.2} = 1 := by
  have hm := idealRitzAdaptiveInertiaGood_measurable kernels T hT S hS q j ε searchAccuracy
    (fun z : X × AdaptiveInertiaTape k cap N => l z.1)
    (fun z : X × AdaptiveInertiaTape k cap N => u z.1)
    (hl.comp measurable_fst) (hu.comp measurable_fst)
    (fun z => hlpos z.1) (fun z => hlu z.1)
    (fun z => samples z.1) (hsamples.comp measurable_fst) Prod.snd measurable_snd
  have ha := idealRitzAdaptiveInertiaGood_prod_ae μ kernels T hT S hS q j ε searchAccuracy
    l u hl hu hlpos hlu samples hsamples
  have hfull := (ae_iff_measure_eq hm.nullMeasurableSet).mp ha
  rw [Measure.real,hfull]
  simp

end
end HierarchicalAbsoluteSpectral
