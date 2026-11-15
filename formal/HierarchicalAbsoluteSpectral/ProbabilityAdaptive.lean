import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real

/-!
Uniform conditional fiber budgets for finite independent random arrays.
The events may depend on earlier coordinates; the fiber hypothesis fixes
all the other coordinates, so no unproved independence of adaptive events
is asserted. First-failure events can be used to restrict guarantees to
histories on which the preceding deterministic invariants hold.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

theorem finite_product_fiber_bound {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n+1)) (E : Set (∀ i, X i)) (hE : MeasurableSet E) (b : ℝ≥0∞)
    (hf : ∀ x : ∀ j : Fin n, X (i.succAbove j),
      μ i {y | i.insertNth y x ∈ E} ≤ b) : Measure.pi μ E ≤ b := by
  let e := MeasurableEquiv.piFinSuccAbove X i
  have hp := MeasurePreserving.symm e (measurePreserving_piFinSuccAbove μ i)
  have hm : MeasurableSet (e.symm ⁻¹' E) := e.symm.measurable hE
  calc
    _ = ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) (e.symm ⁻¹' E) :=
      (hp.measure_preimage_emb e.symm.measurableEmbedding E).symm
    _ = ∫⁻ x, μ i ((fun y => (y,x)) ⁻¹' (e.symm ⁻¹' E))
        ∂Measure.pi (fun j => μ (i.succAbove j)) := Measure.prod_apply_symm hm
    _ ≤ ∫⁻ _x, b ∂Measure.pi (fun j : Fin n => μ (i.succAbove j)) := by
      apply lintegral_mono
      intro x
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact hf x
    _ = b := by simp

theorem finite_product_failure_budget {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : Fin (n+1) → Set (∀ i, X i)) (hE : ∀ i, MeasurableSet (E i))
    (δ : Fin (n+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hf : ∀ (i : Fin (n+1)) (x : ∀ j : Fin n, X (i.succAbove j)),
      μ i {y | i.insertNth y x ∈ E i} ≤ ENNReal.ofReal (δ i)) :
    (Measure.pi μ).real (⋃ i, E i) ≤ ∑ i, δ i ∧
      (Measure.pi μ).real (⋂ i, (E i)ᶜ) ≥ 1-∑ i, δ i := by
  have hsingle (i : Fin (n+1)) : (Measure.pi μ).real (E i) ≤ δ i := by
    have hb := finite_product_fiber_bound μ i (E i) (hE i) (ENNReal.ofReal (δ i)) (hf i)
    have ht := ENNReal.toReal_mono (by finiteness) hb
    simpa only [measureReal_def, ENNReal.toReal_ofReal (hδ i)] using ht
  have hbad : (Measure.pi μ).real (⋃ i, E i) ≤ ∑ i, δ i :=
    (measureReal_iUnion_fintype_le E).trans (Finset.sum_le_sum (fun i _ => hsingle i))
  refine ⟨hbad,?_⟩
  rw [← Set.compl_iUnion, measureReal_compl (MeasurableSet.iUnion hE), probReal_univ]
  linarith

theorem independent_product_failure_on_good
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Ω) (hG : MeasurableSet G) (B : Set (Ω × Ξ)) (hB : MeasurableSet B)
    (β : ℝ) (hβ : 0 ≤ β)
    (hf : ∀ x ∈ G, ν ((fun y => (x,y)) ⁻¹' B) ≤ ENNReal.ofReal β) :
    (μ.prod ν).real B ≤ μ.real Gᶜ+β := by
  let F : Set (Ω × Ξ) := (Prod.fst ⁻¹' G) ∩ B
  have hF : MeasurableSet F := (measurable_fst hG).inter hB
  have hbound : (μ.prod ν) F ≤ ENNReal.ofReal β := by
    rw [Measure.prod_apply hF]
    calc
      _ ≤ ∫⁻ _x : Ω, ENNReal.ofReal β ∂μ := by
        apply lintegral_mono
        intro x
        change ν (Prod.mk x ⁻¹' F) ≤ ENNReal.ofReal β
        by_cases hx : x ∈ G
        · have heq : Prod.mk x ⁻¹' F = Prod.mk x ⁻¹' B := by
            ext y
            simp [F, hx]
          rw [heq]
          exact hf x hx
        · have heq : Prod.mk x ⁻¹' F = ∅ := by ext y; simp [F, hx]
          rw [heq, measure_empty]
          exact bot_le
      _ = _ := by simp
  have hFr : (μ.prod ν).real F ≤ β := by
    have ht := ENNReal.toReal_mono (by finiteness) hbound
    simpa only [measureReal_def, ENNReal.toReal_ofReal hβ] using ht
  have hsub : B ⊆ (Prod.fst ⁻¹' Gᶜ) ∪ F := by
    intro p hp
    by_cases hx : p.1 ∈ G
    · exact Or.inr ⟨hx,hp⟩
    · exact Or.inl hx
  have hpre : (μ.prod ν).real (Prod.fst ⁻¹' Gᶜ) = μ.real Gᶜ :=
    measurePreserving_fst.measureReal_preimage hG.compl.nullMeasurableSet
  calc
    _ ≤ (μ.prod ν).real ((Prod.fst ⁻¹' Gᶜ) ∪ F) := measureReal_mono hsub (by finiteness)
    _ ≤ (μ.prod ν).real (Prod.fst ⁻¹' Gᶜ)+(μ.prod ν).real F := measureReal_union_le _ _
    _ ≤ _ := by rw [hpre]; linarith

end
end HierarchicalAbsoluteSpectral
