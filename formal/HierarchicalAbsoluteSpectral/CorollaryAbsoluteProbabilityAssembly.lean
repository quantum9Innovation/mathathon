import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityEvent
import HierarchicalAbsoluteSpectral.ProbabilityMainTapeGood

/-! Fixed-threshold events are assembled for all ranks `0,...,m` before
executing the doubling controller. Only a finite union bound is needed;
the controller may choose any subset of these ranks from its earlier answers. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem probability_finite_product_common_event
    {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, Set (X i)) (β : ℝ)
    (hEm : ∀ i, MeasurableSet (E i)) (hEp : ∀ i, 1-β ≤ (μ i).real (E i)) :
    MeasurableSet {z : ∀ i, X i | ∀ i, z i ∈ E i} ∧
      1-(Fintype.card ι:ℝ)*β ≤ (Measure.pi μ).real {z : ∀ i, X i | ∀ i, z i ∈ E i} := by
  let F : ι → Set (∀ i, X i) := fun i => (fun z => z i) ⁻¹' E i
  apply probability_finite_common_event (Measure.pi μ) F β
  · intro i
    exact (hEm i).preimage (measurable_pi_apply i)
  · intro i
    change 1-β ≤ (Measure.pi μ).real ((fun z => z i) ⁻¹' E i)
    rw [(measurePreserving_eval μ i).measureReal_preimage (hEm i).nullMeasurableSet]
    exact hEp i

/-- All rank events share the same fixed threshold and stored sketches.
The event includes rank zero and handles full-support ranks by `univ`. -/
theorem MainSketchGood.absolute_all_ranks_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : {t : ℝ // 0 < t}) :
    ∃ E : Set (∀ s : Fin (m+1), AbsoluteProbabilityTape m s.val I.repetitions), MeasurableSet E ∧
      (Measure.pi (fun s : Fin (m+1) => absoluteProbabilityLaw m s.val I.repetitions)).real E ≥
        1-((m:ℝ)+1)*(I.queryFailure+I.singleFailure) ∧
      ∀ z ∈ E, ∀ (s : Fin (m+1)) (hs : s.val < C.pair.dimension),
        AbsoluteRankThresholdGood kernels I S C s.val hs (by omega) t
          (absoluteProbabilityTapeRestriction C.pair.dimension_le_fin (z s)) := by
  classical
  let β := I.queryFailure+I.singleFailure
  have hβ : 0 ≤ β := add_nonneg I.queryFailure_positive.le I.singleFailure_positive.le
  have hsingle (s : Fin (m+1)) :
      ∃ F : Set (AbsoluteProbabilityTape m s.val I.repetitions), MeasurableSet F ∧
        (absoluteProbabilityLaw m s.val I.repetitions).real F ≥ 1-β ∧
        ∀ z ∈ F, ∀ hs : s.val < C.pair.dimension,
          AbsoluteRankThresholdGood kernels I S C s.val hs (by omega) t
            (absoluteProbabilityTapeRestriction C.pair.dimension_le_fin z) := by
    by_cases hs : s.val < C.pair.dimension
    · obtain ⟨F,hFm,hFp,hF⟩ := hg.absolute_rank_good_event kernels I S C s.val hs (by omega) t
      let restr := absoluteProbabilityTapeRestriction (s:=s.val) (N:=I.repetitions) C.pair.dimension_le_fin
      have hp := absoluteProbabilityTapeRestriction_measurePreserving (s:=s.val) (N:=I.repetitions)
        C.pair.dimension_le_fin
      refine ⟨restr ⁻¹' F,hFm.preimage hp.measurable,?_,?_⟩
      · rw [hp.measureReal_preimage hFm.nullMeasurableSet]
        dsimp only [β]
        linarith
      · intro z hz _
        exact hF (restr z) hz
    · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
      · simp only [probReal_univ]
        linarith
      · intro z _ h
        exact False.elim (hs h)
  choose F hFm hFp hF using hsingle
  have hh := probability_finite_product_common_event
    (fun s : Fin (m+1) => absoluteProbabilityLaw m s.val I.repetitions) F β hFm hFp
  refine ⟨{z | ∀ s, z s ∈ F s},hh.1,?_,?_⟩
  · simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,β] using hh.2
  · intro z hz s hs
    exact hF s (z s) (hz s) hs

/-- Finite sketch preprocessing lifts any family of core events to the
original absolute algorithm tape, without an assumed conditional law. -/
theorem absolute_random_finite_core_success (I : AbsoluteProblem n m p L)
    (E : MainSketchSampleTape I.seed → Set (AbsoluteCoreTape I))
    (δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁)
    (hEm : ∀ z, MainSketchGood I.seed (mainSketchFromFiniteSample I.seed z) → MeasurableSet (E z))
    (hEp : ∀ z, MainSketchGood I.seed (mainSketchFromFiniteSample I.seed z) →
      1-δ₁ ≤ (absoluteCoreLaw I).real (E z)) :
    MeasurableSet {g : AbsoluteTape I | MainSketchGood I.seed (mainSketchProgram I.seed g.1).eval ∧
      g.2 ∈ E (mainSketchFiniteSample I.seed g.1)} ∧
      1-I.seed.delta/10-δ₁ ≤ (absoluteRandomLaw I).real
        {g : AbsoluteTape I | MainSketchGood I.seed (mainSketchProgram I.seed g.1).eval ∧
          g.2 ∈ E (mainSketchFiniteSample I.seed g.1)} := by
  let G : Set (MainSketchSampleTape I.seed) :=
    {z | MainSketchGood I.seed (mainSketchFromFiniteSample I.seed z)}
  have hh := finite_preprocessing_success ((mainRandomLaw I.seed).map (mainSketchFiniteSample I.seed))
    (absoluteCoreLaw I) G E (I.seed.delta/10) δ₁ hδ₁
    (mainSketchFinite_marginal_good_probability I.seed) hEm hEp
  have hsketch : MeasurePreserving (mainSketchFiniteSample I.seed) (mainRandomLaw I.seed)
      ((mainRandomLaw I.seed).map (mainSketchFiniteSample I.seed)) :=
    ⟨mainSketchFiniteSample_measurable I.seed,rfl⟩
  have hid : MeasurePreserving (id : AbsoluteCoreTape I → AbsoluteCoreTape I)
      (absoluteCoreLaw I) (absoluteCoreLaw I) := ⟨measurable_id,Measure.map_id⟩
  have hp := hsketch.prod hid
  have he : {g : AbsoluteTape I | MainSketchGood I.seed (mainSketchProgram I.seed g.1).eval ∧
      g.2 ∈ E (mainSketchFiniteSample I.seed g.1)} =
      (fun g : AbsoluteTape I => (mainSketchFiniteSample I.seed g.1,g.2)) ⁻¹'
        {zx : MainSketchSampleTape I.seed × AbsoluteCoreTape I | zx.1 ∈ G ∧ zx.2 ∈ E zx.1} := by
    ext g
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [mainSketchProgram_factorization]
    rfl
  rw [he]
  refine ⟨hh.1.preimage hp.measurable,?_⟩
  change 1-I.seed.delta/10-δ₁ ≤
    ((mainRandomLaw I.seed).prod (absoluteCoreLaw I)).real
      (Prod.map (mainSketchFiniteSample I.seed) id ⁻¹'
        {zx : MainSketchSampleTape I.seed × AbsoluteCoreTape I | zx.1 ∈ G ∧ zx.2 ∈ E zx.1})
  rw [hp.measureReal_preimage hh.1.nullMeasurableSet]
  exact hh.2

end
end HierarchicalAbsoluteSpectral
