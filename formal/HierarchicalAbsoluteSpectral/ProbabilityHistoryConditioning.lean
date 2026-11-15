import HierarchicalAbsoluteSpectral.ProbabilityAdaptive

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

theorem measurable_history_fresh_success {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Set Ω) (hHm : MeasurableSet H) (E : Set (Ω × X)) (hEm : MeasurableSet E)
    (δ₀ δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁) (hHp : 1-δ₀ ≤ μ.real H)
    (hEp : ∀ ω ∈ H, 1-δ₁ ≤ ν.real (Prod.mk ω ⁻¹' E)) :
    MeasurableSet ((Prod.fst ⁻¹' H) ∩ E) ∧
      1-δ₀-δ₁ ≤ (μ.prod ν).real ((Prod.fst ⁻¹' H) ∩ E) := by
  let F := (Prod.fst ⁻¹' H) ∩ E
  have hFm : MeasurableSet F := (hHm.preimage measurable_fst).inter hEm
  refine ⟨hFm,?_⟩
  have hb := independent_product_failure_on_good μ ν H hHm Fᶜ hFm.compl δ₁ hδ₁ (by
    intro ω hω
    have he : Prod.mk ω ⁻¹' Fᶜ=(Prod.mk ω ⁻¹' E)ᶜ := by ext x; simp [F,hω]
    rw [he]
    have hp := hEp ω hω
    have hm : MeasurableSet (Prod.mk ω ⁻¹' E) := hEm.preimage (measurable_const.prodMk measurable_id)
    have hc : ν.real ((Prod.mk ω ⁻¹' E)ᶜ) ≤ δ₁ := by
      rw [measureReal_compl hm,probReal_univ]
      linarith
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    simpa only [measureReal_def,ENNReal.toReal_ofReal hδ₁] using hc)
  have hc : μ.real Hᶜ ≤ δ₀ := by
    rw [measureReal_compl hHm,probReal_univ]
    linarith
  rw [measureReal_compl hFm,probReal_univ] at hb
  linarith

end
end HierarchicalAbsoluteSpectral
