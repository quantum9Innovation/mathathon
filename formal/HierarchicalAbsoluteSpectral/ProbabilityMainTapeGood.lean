import HierarchicalAbsoluteSpectral.ProbabilityMainTapeLaw
import HierarchicalAbsoluteSpectral.MainSketchFiniteProbability
import HierarchicalAbsoluteSpectral.ProbabilityFiniteConditioning

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
variable {n m p r L : ℕ}

theorem mainSketchFinite_marginal_good_probability (I : FixedProblem n m p r L) :
    ((mainRandomLaw I).map (mainSketchFiniteSample I)).real
      {z | MainSketchGood I (mainSketchFromFiniteSample I z)} ≥ 1-I.delta/10 := by
  have hm : MeasurableSet {z : MainSketchSampleTape I | MainSketchGood I (mainSketchFromFiniteSample I z)} :=
    (Set.to_countable _).measurableSet
  change (((mainRandomLaw I).map (mainSketchFiniteSample I))
    {z | MainSketchGood I (mainSketchFromFiniteSample I z)}).toReal ≥ _
  rw [Measure.map_apply (mainSketchFiniteSample_measurable I) hm]
  exact mainSketchFiniteSample_good_probability I

/-- Conditional later-stage guarantees lift to the single original Gaussian tape. -/
theorem main_random_finite_core_success (I : FixedProblem n m p r L)
    (E : MainSketchSampleTape I → Set (MainCoreTapeOriginal I)) (δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁)
    (hEm : ∀ z, MainSketchGood I (mainSketchFromFiniteSample I z) → MeasurableSet (E z))
    (hEp : ∀ z, MainSketchGood I (mainSketchFromFiniteSample I z) →
      1-δ₁ ≤ (mainCoreLawOriginal I).real (E z)) :
    MeasurableSet {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval ∧
      mainCoreTapeOriginal I g ∈ E (mainSketchFiniteSample I g)} ∧
      1-I.delta/10-δ₁ ≤ (mainRandomLaw I).real
        {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval ∧
          mainCoreTapeOriginal I g ∈ E (mainSketchFiniteSample I g)} := by
  let G : Set (MainSketchSampleTape I) := {z | MainSketchGood I (mainSketchFromFiniteSample I z)}
  have hh := finite_preprocessing_success ((mainRandomLaw I).map (mainSketchFiniteSample I))
    (mainCoreLawOriginal I) G E (I.delta/10) δ₁ hδ₁
    (mainSketchFinite_marginal_good_probability I) hEm hEp
  have hp := mainSketchFiniteSample_coreTape_measurePreserving I
  have he : {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval ∧
      mainCoreTapeOriginal I g ∈ E (mainSketchFiniteSample I g)} =
      (fun g => (mainSketchFiniteSample I g,mainCoreTapeOriginal I g)) ⁻¹'
        {zx : MainSketchSampleTape I × MainCoreTapeOriginal I | zx.1 ∈ G ∧ zx.2 ∈ E zx.1} := by
    ext g
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [mainSketchProgram_factorization]
    rfl
  rw [he]
  refine ⟨hh.1.preimage hp.measurable,?_⟩
  rw [hp.measureReal_preimage hh.1.nullMeasurableSet]
  exact hh.2

end
end HierarchicalAbsoluteSpectral
