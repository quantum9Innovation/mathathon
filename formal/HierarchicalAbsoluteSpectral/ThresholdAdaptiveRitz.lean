import HierarchicalAbsoluteSpectral.ThresholdAdaptiveProbability

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r N cap : ℕ}
local instance adaptiveMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance adaptiveMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

def positiveRitzDecision (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k) (ε : ℝ)
    (G : Fin N → Fin r → Fin k → ℝ) (t : ℝ) : ThresholdDecision :=
  if ht : 0 < t then thresholdDecision
    (fun trial => gaussianRitzObservable kernels q j ((T ⟨t,ht⟩,S ⟨t,ht⟩),G trial)) ε else .below

def idealRitzDecisions (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k) (ε : ℝ)
    (samples : Fin cap → Fin N → Fin r → Fin k → ℝ) (i : Fin cap) : ℝ → ThresholdDecision :=
  positiveRitzDecision kernels T S q j ε (samples i)

theorem idealRitzHistory_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (n : ℕ) (hn : n ≤ cap) :
    Measurable (fun samples : Fin cap → Fin N → Fin r → Fin k → ℝ =>
      thresholdQueryHistory (idealRitzDecisions kernels T S q j ε samples) searchAccuracy l u n hn) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let i : Fin cap := ⟨n,by omega⟩
    let state := fun samples : Fin cap → Fin N → Fin r → Fin k → ℝ =>
      thresholdQueryHistory (idealRitzDecisions kernels T S q j ε samples) searchAccuracy l u n (by omega)
    have hs : Measurable state := ih (by omega)
    have hm : Measurable (fun samples => ((state samples).1+(state samples).2.1)/2) :=
      (hs.fst.add hs.snd.fst).div_const 2
    have hpos : ∀ samples, 0 < ((state samples).1+(state samples).2.1)/2 := fun samples =>
      thresholdQueryHistory_midpoint_positive _ searchAccuracy l u hl hlu i
    let time := fun samples => (⟨((state samples).1+(state samples).2.1)/2,hpos samples⟩ : {t : ℝ // 0 < t})
    have htime : Measurable time := hm.subtype_mk
    have hparams : Measurable (fun samples => (T (time samples),S (time samples))) :=
      (hT.comp htime).prodMk (hS.comp htime)
    have hvalue : ∀ trial : Fin N, Measurable (fun samples =>
        gaussianRitzObservable kernels q j ((T (time samples),S (time samples)),samples i trial)) := by
      intro trial
      exact (gaussianRitzObservable_measurable kernels q j).comp
        (hparams.prodMk ((measurable_pi_apply trial).comp (measurable_pi_apply i)))
    have hanswer : Measurable (fun samples =>
        idealRitzDecisions kernels T S q j ε samples i (((state samples).1+(state samples).2.1)/2)) := by
      convert thresholdDecision_measurable _ hvalue ε using 1
      funext samples
      simp only [idealRitzDecisions,positiveRitzDecision,dif_pos (hpos samples)]
      rfl
    exact thresholdQueryStep_measurable_of_answer
      (idealRitzDecisions kernels T S q j ε) searchAccuracy i state hs hanswer

def idealRitzThresholdParameter
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k)
    (ε searchAccuracy l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin r → Fin k → ℝ) (i : Fin cap) : {t : ℝ // 0 < t} :=
  ⟨((thresholdQueryHistory (idealRitzDecisions kernels T S q j ε samples)
      searchAccuracy l u i.val i.isLt.le).1+
    (thresholdQueryHistory (idealRitzDecisions kernels T S q j ε samples)
      searchAccuracy l u i.val i.isLt.le).2.1)/2,
    thresholdQueryHistory_midpoint_positive _ searchAccuracy l u hl hlu i⟩

theorem idealRitzThresholdParameter_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) (i : Fin cap) :
    Measurable (fun samples : Fin cap → Fin N → Fin r → Fin k → ℝ =>
      idealRitzThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu samples i) := by
  have hs := idealRitzHistory_measurable (r:=r) (N:=N) kernels T hT S hS q j ε searchAccuracy l u hl hlu i.val i.isLt.le
  exact ((hs.fst.add hs.snd.fst).div_const 2).subtype_mk

theorem idealRitzThresholdParameter_update
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k)
    (ε searchAccuracy l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (samples : Fin cap → Fin N → Fin r → Fin k → ℝ) (i : Fin cap)
    (fresh : Fin N → Fin r → Fin k → ℝ) :
    idealRitzThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu
      (Function.update samples i fresh) i =
    idealRitzThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu samples i := by
  apply Subtype.ext
  exact congrArg (fun state : ThresholdQueryState => (state.1+state.2.1)/2)
    (thresholdQueryHistory_current_update (fun _ G t => positiveRitzDecision kernels T S q j ε G t)
      samples searchAccuracy l u i fresh)

end
end HierarchicalAbsoluteSpectral
