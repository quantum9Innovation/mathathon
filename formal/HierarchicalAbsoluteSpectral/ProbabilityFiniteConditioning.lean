import HierarchicalAbsoluteSpectral.ProbabilityAdaptive

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

/-- Finite preprocessing may select an arbitrary later measurable success event. -/
theorem finite_preprocessing_success
    {Z X : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] (μ : Measure Z) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Z) (E : Z → Set X) (δ₀ δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁)
    (hG : 1-δ₀ ≤ μ.real G) (hEm : ∀ z ∈ G, MeasurableSet (E z))
    (hEp : ∀ z ∈ G, 1-δ₁ ≤ ν.real (E z)) :
    MeasurableSet {zx : Z × X | zx.1 ∈ G ∧ zx.2 ∈ E zx.1} ∧
      1-δ₀-δ₁ ≤ (μ.prod ν).real {zx : Z × X | zx.1 ∈ G ∧ zx.2 ∈ E zx.1} := by
  classical
  let F : Set (Z × X) := {zx | zx.1 ∈ G ∧ zx.2 ∈ E zx.1}
  have hGm : MeasurableSet G := (Set.to_countable _).measurableSet
  have hFm : MeasurableSet F := by
    have he : F = ⋃ z : Z, ({z} ×ˢ (if z ∈ G then E z else ∅)) := by
      ext zx
      simp [F]
    rw [he]
    apply MeasurableSet.iUnion
    intro z
    apply MeasurableSet.prod (measurableSet_singleton z)
    split_ifs with hz
    · exact hEm z hz
    · exact MeasurableSet.empty
  refine ⟨hFm,?_⟩
  have hb := independent_product_failure_on_good μ ν G hGm Fᶜ hFm.compl δ₁ hδ₁ (by
    intro z hz
    have he : Prod.mk z ⁻¹' Fᶜ = (E z)ᶜ := by ext x; simp [F,hz]
    rw [he]
    have hp := hEp z hz
    have hc : ν.real ((E z)ᶜ) ≤ δ₁ := by
      rw [measureReal_compl (hEm z hz),probReal_univ]
      linarith
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    simpa only [measureReal_def,ENNReal.toReal_ofReal hδ₁] using hc)
  have hc : μ.real Gᶜ ≤ δ₀ := by
    rw [measureReal_compl hGm,probReal_univ]
    linarith
  rw [measureReal_compl hFm,probReal_univ] at hb
  linarith

end
end HierarchicalAbsoluteSpectral
