import HierarchicalAbsoluteSpectral.ThresholdQueryHistory

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory

instance thresholdDecisionFintype : Fintype ThresholdDecision where
  elems := {.below,.above,.near}
  complete := by intro d; cases d <;> simp

instance thresholdDecisionMeasurableSpace : MeasurableSpace ThresholdDecision := ⊤

theorem thresholdDecision_measurable {X : Type*} [MeasurableSpace X] {N : ℕ}
    (values : Fin N → X → ℝ) (hvalues : ∀ i, Measurable (values i)) (ε : ℝ) :
    Measurable (fun x => thresholdDecision (fun i => values i x) ε) := by
  have hOne : MeasurableSet {x | ∃ i, 1<values i x} := by
    simpa only [Set.setOf_exists] using
      MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const (hvalues i))
  have hLow : MeasurableSet {x | ∀ i, values i x≤1-2*ε} := by
    simpa only [Set.setOf_forall] using
      MeasurableSet.iInter (fun i => measurableSet_le (hvalues i) measurable_const)
  exact Measurable.ite hOne measurable_const (Measurable.ite hLow measurable_const measurable_const)

theorem thresholdQueryStep_measurable {X : Type*} [MeasurableSpace X] {cap : ℕ}
    (query : X → Fin cap → ℝ → ThresholdDecision)
    (hquery : ∀ i, Measurable (fun x : X × ℝ => query x.1 i x.2))
    (ε : ℝ) (i : Fin cap) (state : X → ThresholdQueryState) (hstate : Measurable state) :
    Measurable (fun x => thresholdQueryStep (query x) ε i (state x)) := by
  have hl := hstate.fst
  have hu := hstate.snd.fst
  have ha := hstate.snd.snd
  have ht : Measurable (fun x => ((state x).1+(state x).2.1)/2) := (hl.add hu).div_const 2
  have hq : Measurable (fun x => query x i (((state x).1+(state x).2.1)/2)) :=
    (hquery i).comp (measurable_id.prodMk ht)
  have hActive : MeasurableSet {x | (state x).2.2=true} := measurableSet_eq_fun ha measurable_const
  have hStop : MeasurableSet {x | (state x).2.1-(state x).1≤ε*(state x).1} :=
    measurableSet_le (hu.sub hl) (measurable_const.mul hl)
  have hBelow : MeasurableSet {x | query x i (((state x).1+(state x).2.1)/2)=.below} :=
    measurableSet_eq_fun hq measurable_const
  have hAbove : MeasurableSet {x | query x i (((state x).1+(state x).2.1)/2)=.above} :=
    measurableSet_eq_fun hq measurable_const
  have hSameFalse : Measurable (fun x => ((state x).1,(state x).2.1,false)) :=
    hl.prodMk (hu.prodMk measurable_const)
  have hNewBelow : Measurable (fun x => (((state x).1+(state x).2.1)/2,(state x).2.1,true)) :=
    ht.prodMk (hu.prodMk measurable_const)
  have hNewAbove : Measurable (fun x => ((state x).1,((state x).1+(state x).2.1)/2,true)) :=
    hl.prodMk (ht.prodMk measurable_const)
  exact Measurable.ite hActive (Measurable.ite hStop hSameFalse
    (Measurable.ite hBelow hNewBelow (Measurable.ite hAbove hNewAbove hSameFalse))) hstate

theorem thresholdQueryHistory_measurable {X : Type*} [MeasurableSpace X] {cap : ℕ}
    (query : X → Fin cap → ℝ → ThresholdDecision)
    (hquery : ∀ i, Measurable (fun x : X × ℝ => query x.1 i x.2))
    (ε : ℝ) (l u : X → ℝ) (hl : Measurable l) (hu : Measurable u)
    (n : ℕ) (hn : n≤cap) :
    Measurable (fun x => thresholdQueryHistory (query x) ε (l x) (u x) n hn) := by
  induction n with
  | zero => exact hl.prodMk (hu.prodMk measurable_const)
  | succ n ih =>
    exact thresholdQueryStep_measurable query hquery ε ⟨n,by omega⟩ _ (ih (by omega))

end
end HierarchicalAbsoluteSpectral
