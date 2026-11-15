import HierarchicalAbsoluteSpectral.MainCoreProbabilityTape
import HierarchicalAbsoluteSpectral.MainAdaptiveInitialEndpoints
import HierarchicalAbsoluteSpectral.MainStatementsQueryViews
import HierarchicalAbsoluteSpectral.ThresholdSelection

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector gaussianRitzObservable

private def corePositiveValue (t : ℝ) : ℝ := if 0 < t then t else 1

private theorem corePositiveValue_pos (t : ℝ) : 0 < corePositiveValue t := by
  unfold corePositiveValue
  split_ifs with ht
  · exact ht
  · norm_num

private def corePositiveTime (t : ℝ) : {t : ℝ // 0 < t} :=
  ⟨corePositiveValue t,corePositiveValue_pos t⟩

private theorem corePositiveTime_measurable : Measurable corePositiveTime :=
  (Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_id measurable_const).subtype_mk

theorem mainCoreIdealQuery_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (i : Fin I.queryCap) :
    Measurable (fun x : MainCoreQueryTape I C.pair.dimension × ℝ =>
      mainIdealQuery kernels I S C hr x.1 i x.2) := by
  let time := fun x : MainCoreQueryTape I C.pair.dimension × ℝ => corePositiveTime x.2
  have ht : Measurable time := corePositiveTime_measurable.comp measurable_snd
  have hp := ((mainThresholdView_measurable kernels I S C).comp ht).prodMk
    ((mainSourceView_measurable kernels I S C).comp ht)
  have hv : ∀ trial : Fin I.repetitions, Measurable (fun x : MainCoreQueryTape I C.pair.dimension × ℝ =>
      gaussianRitzObservable kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩
        ((mainThresholdView kernels I S C (time x),mainSourceView kernels I S C (time x)),x.1 i trial)) := by
    intro trial
    exact (gaussianRitzObservable_measurable kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩).comp
      (hp.prodMk ((measurable_pi_apply trial).comp ((measurable_pi_apply i).comp measurable_fst)))
  have hm : Measurable (fun x : MainCoreQueryTape I C.pair.dimension × ℝ =>
      if 0 < x.2 then thresholdDecision (fun trial =>
        gaussianRitzObservable kernels (mainKrylovDegree I S C hr) ⟨r,hr⟩
          ((mainThresholdView kernels I S C (time x),mainSourceView kernels I S C (time x)),x.1 i trial))
        (mainRitzAccuracy I) else .below) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      (thresholdDecision_measurable _ hv (mainRitzAccuracy I)) measurable_const
  convert hm using 1
  funext x
  by_cases hx : 0 < x.2
  · have he : time x = ⟨x.2,hx⟩ := by
      apply Subtype.ext
      exact if_pos hx
    simp only [mainIdealQuery,idealRitzDecisions,positiveRitzDecision,dif_pos hx,if_pos hx,he]
  · simp only [mainIdealQuery,idealRitzDecisions,positiveRitzDecision,dif_neg hx,if_neg hx]

theorem thresholdSearchIndexedValue_selected_measurable {X : Type*} [MeasurableSpace X] {cap : ℕ}
    (query : X → Fin cap → ℝ → ThresholdDecision)
    (hquery : ∀ i, Measurable (fun z : X × ℝ => query z.1 i z.2))
    (ε : ℝ) (fuel offset : ℕ) (hcap : offset+fuel ≤ cap)
    (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u) :
    Measurable (fun x => (thresholdSearchIndexedValue (query x) ε fuel offset hcap (l x) (u x)).selected) := by
  classical
  induction fuel generalizing offset l u with
  | zero => exact hu
  | succ fuel ih =>
    let mid := fun x => (l x+u x)/2
    have hmid : Measurable mid := (hl.add hu).div_const 2
    have hstop : MeasurableSet {x : X | u x-l x ≤ ε*l x} :=
      measurableSet_le (hu.sub hl) (measurable_const.mul hl)
    have hanswer : Measurable (fun x : X => query x ⟨offset,by omega⟩ (mid x)) :=
      (hquery ⟨offset,by omega⟩).comp (measurable_id.prodMk hmid)
    have hbelow := measurableSet_eq_fun hanswer (measurable_const (a:=ThresholdDecision.below))
    have habove := measurableSet_eq_fun hanswer (measurable_const (a:=ThresholdDecision.above))
    have hb := ih (offset+1) (by omega) mid u hmid hu
    have ha := ih (offset+1) (by omega) l mid hl hmid
    have hm : Measurable (fun x : X =>
        if u x-l x ≤ ε*l x then u x else
        if query x ⟨offset,by omega⟩ (mid x) = .below then
          (thresholdSearchIndexedValue (query x) ε fuel (offset+1) (by omega) (mid x) (u x)).selected else
        if query x ⟨offset,by omega⟩ (mid x) = .above then
          (thresholdSearchIndexedValue (query x) ε fuel (offset+1) (by omega) (l x) (mid x)).selected else
        mid x) :=
      Measurable.ite hstop hu (Measurable.ite hbelow hb (Measurable.ite habove ha hmid))
    convert hm using 1
    funext x
    simp only [thresholdSearchIndexedValue]
    by_cases hs : u x-l x ≤ ε*l x
    · simp only [if_pos hs,ThresholdSearchResult.selected]
    · simp only [if_neg hs]
      dsimp only [mid]
      cases hd : query x ⟨offset,by omega⟩ ((l x+u x)/2) <;>
        simp only [reduceCtorEq,ite_true,ite_false,ThresholdSearchResult.selected]

def mainCoreSelectedReal (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreInitialHistory I C.pair.dimension) : ℝ :=
  (thresholdSearchIndexedValue (mainIdealQuery kernels I S C hr x.2) I.nearTolerance
    I.queryCap 0 (by omega)
    (mainInitializerLowerEndpoint kernels C.rightGram (columnsMatrix x.1) I.singleFailure)
    (mainInitializerUpperEndpoint kernels C.rightGram (columnsMatrix x.1))).selected

theorem mainCoreSelectedReal_pos (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreInitialHistory I C.pair.dimension) :
    0 < mainCoreSelectedReal kernels I S C hr x :=
  thresholdSearchIndexedValue_selected_positive _ _ _ _ _ _ _
    (mainInitializerLowerEndpoint_pos kernels C.rightGram (columnsMatrix x.1) I.singleFailure
      (by omega) (div_pos I.delta_positive (by norm_num)))
    (mainInitializerEndpoints_ordered kernels C.rightGram (columnsMatrix x.1) I.singleFailure
      (by omega) (div_pos I.delta_positive (by norm_num)))

theorem mainCoreSelectedReal_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    Measurable (mainCoreSelectedReal kernels I S C hr) := by
  unfold mainCoreSelectedReal
  refine thresholdSearchIndexedValue_selected_measurable
    (X:=MainCoreInitialHistory I C.pair.dimension)
    (fun x i t => mainIdealQuery kernels I S C hr x.2 i t) ?_
    I.nearTolerance I.queryCap 0 (by omega) _ _ ?_ ?_
  · intro i
    exact (mainCoreIdealQuery_measurable kernels I S C hr i).comp
      (measurable_fst.snd.prodMk measurable_snd)
  · exact (mainInitializerLowerEndpoint_gaussian_measurable (r:=r)
      kernels C.rightGram I.singleFailure).comp measurable_fst
  · exact (mainInitializerUpperEndpoint_gaussian_measurable (r:=r)
      kernels C.rightGram).comp measurable_fst

def mainCoreSelectedThreshold (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (x : MainCoreInitialHistory I C.pair.dimension) : {t : ℝ // 0 < t} :=
  ⟨mainCoreSelectedReal kernels I S C hr x,mainCoreSelectedReal_pos kernels I S C hr x⟩

theorem mainCoreSelectedThreshold_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    Measurable (mainCoreSelectedThreshold kernels I S C hr) :=
  (mainCoreSelectedReal_measurable kernels I S C hr).subtype_mk

end
end HierarchicalAbsoluteSpectral
