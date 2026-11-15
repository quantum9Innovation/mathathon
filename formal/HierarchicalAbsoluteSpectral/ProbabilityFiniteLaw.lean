import HierarchicalAbsoluteSpectral.GaussianPriority
import HierarchicalAbsoluteSpectral.GaussianSigns
import SRHT.Model

/-! Connect actual Mathlib sampling measures to the imported explicit
finite-law probabilities. This is equality of the event probabilities,
not an assumption that a finite-law draw is a primitive instruction. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set SparseFock

theorem probability_eq_finiteLaw_of_fibers
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : FiniteLaw α) (f : Ω → α)
    (hf : Measurable f) (hmass : ∀ a, μ.real {x | f x = a} = ν.weight a)
    (E : Set α) : μ.real (f ⁻¹' E) = ν.prob E := by
  classical
  let F := Finset.univ.filter (fun a : α => a ∈ E)
  have hF : (F : Set α) = E := by ext a; simp [F]
  have hs := sum_measureReal_preimage_singleton (μ := μ) (f := f) F
    (fun a _ => hf (measurableSet_singleton a))
  rw [hF] at hs
  have hm (a : α) : μ.real (f ⁻¹' {a}) = ν.weight a := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using hmass a
  simp_rw [hm] at hs
  rw [← hs]
  simp [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator, F, Finset.sum_filter]

theorem finiteLaw_product_sampler_probability
    {Ω Ξ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) (ξ : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure ξ]
    (ν : FiniteLaw α) (τ : FiniteLaw β) (f : Ω → α) (g : Ξ → β)
    (hf : Measurable f) (hg : Measurable g)
    (hmass : ∀ a, μ.real {x | f x = a} = ν.weight a)
    (hnmass : ∀ b, ξ.real {x | g x = b} = τ.weight b)
    (E : Set (α × β)) :
    (μ.prod ξ).real ((fun x => (f x.1,g x.2)) ⁻¹' E) = (ν.product τ).prob E := by
  apply probability_eq_finiteLaw_of_fibers (μ.prod ξ) (ν.product τ) _
    ((hf.comp measurable_fst).prodMk (hg.comp measurable_snd)) _ E
  rintro ⟨a,b⟩
  change (μ.prod ξ).real {x : Ω × Ξ | (f x.1,g x.2) = (a,b)} = (ν.product τ).weight (a,b)
  have heq : {x : Ω × Ξ | (f x.1,g x.2) = (a,b)} =
      {x | f x = a} ×ˢ {x | g x = b} := by ext x; simp
  rw [heq, measureReal_prod_prod, hmass, hnmass, FiniteLaw.product_weight]

def priorityUniformLaw (n M : ℕ) (hM : M ≤ n) : FiniteLaw (PriorityRowSet n M) := by
  letI : Nonempty (PriorityRowSet n M) := priorityRowSet_nonempty n M hM
  exact SRHT.uniformLaw _

theorem priorityRowSet_finiteLaw_probability (n M : ℕ) (hM : M ≤ n)
    (E : Set (PriorityRowSet n M)) :
    (gaussianVector n).real (priorityRowSet n M hM ⁻¹' E) =
      (priorityUniformLaw n M hM).prob E := by
  letI : Nonempty (PriorityRowSet n M) := priorityRowSet_nonempty n M hM
  apply probability_eq_finiteLaw_of_fibers _ _ _ (priorityRowSet_measurable n M hM) _ E
  exact gaussian_priority_singleton_probability n M hM

end
end HierarchicalAbsoluteSpectral
