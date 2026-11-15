import HierarchicalAbsoluteSpectral.ThresholdHistoryMeasurable
import HierarchicalAbsoluteSpectral.ProbabilityAdaptive

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- A finite adaptive union bound. The parameter used at query i is Borel
and is unchanged when only the fresh i-th random block is changed. -/
theorem adaptive_finite_failure_probability {X P : Type*} [MeasurableSpace X]
    [MeasurableSpace P] [Inhabited X] (μ : Measure X) [IsProbabilityMeasure μ]
    (cap : ℕ) (parameter : (Fin cap → X) → Fin cap → P)
    (hparameter : ∀ i, Measurable (fun samples => parameter samples i))
    (hignore : ∀ samples i x, parameter (Function.update samples i x) i=parameter samples i)
    (bad : Set (P × X)) (hbad : MeasurableSet bad) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfiber : ∀ p, μ {x | (p,x) ∈ bad} ≤ ENNReal.ofReal δ) :
    (Measure.pi (fun _ : Fin cap => μ)).real
        (⋃ i : Fin cap, {samples | (parameter samples i,samples i) ∈ bad}) ≤ (cap:ℝ)*δ ∧
      (Measure.pi (fun _ : Fin cap => μ)).real
        (⋂ i : Fin cap, {samples | (parameter samples i,samples i) ∈ bad}ᶜ) ≥ 1-(cap:ℝ)*δ := by
  cases cap with
  | zero => simp
  | succ cap =>
    let E : Fin (cap+1) → Set (Fin (cap+1) → X) :=
      fun i => {samples | (parameter samples i,samples i) ∈ bad}
    have hE : ∀ i, MeasurableSet (E i) := fun i =>
      hbad.preimage ((hparameter i).prodMk (measurable_pi_apply i))
    have hb : ∀ (i : Fin (cap+1)) (outside : Fin cap → X),
        μ {x | i.insertNth x outside ∈ E i} ≤ ENNReal.ofReal δ := by
      intro i outside
      let baseline : Fin (cap+1) → X := i.insertNth (default : X) outside
      have heq : {x | i.insertNth x outside ∈ E i}=
          {x | (parameter baseline i,x) ∈ bad} := by
        ext x
        have hi := hignore baseline i x
        rw [show Function.update baseline i x=i.insertNth x outside from
          Fin.update_insertNth (α:=fun _ : Fin (cap+1) => X) i default x outside] at hi
        simp only [E,Set.mem_setOf_eq,hi,Fin.insertNth_apply_same]
      rw [heq]
      exact hfiber _
    have hh := finite_product_failure_budget (fun _ : Fin (cap+1) => μ) E hE
      (fun _ => δ) (fun _ => hδ) hb
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using hh

theorem thresholdQueryStep_measurable_of_answer {X : Type*} [MeasurableSpace X] {cap : ℕ}
    (query : X → Fin cap → ℝ → ThresholdDecision) (ε : ℝ) (i : Fin cap)
    (state : X → ThresholdQueryState) (hstate : Measurable state)
    (hanswer : Measurable (fun x => query x i (((state x).1+(state x).2.1)/2))) :
    Measurable (fun x => thresholdQueryStep (query x) ε i (state x)) := by
  exact thresholdQueryStep_measurable
    (fun x _ _ => query x i (((state x).1+(state x).2.1)/2))
    (fun _ => hanswer.comp measurable_fst) ε i state hstate

end
end HierarchicalAbsoluteSpectral
