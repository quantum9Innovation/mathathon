import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityQuery
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteTape

/-! One measurable fixed-threshold event for each possible attempted rank,
with both safe query answers and the carried physical strong certificate.
The conditional strong event is vacuous when its target condition fails;
on a safe accepted answer that condition follows from the query itself. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial Set
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L k s N : ℕ}

theorem probability_inter_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) (a b : ℝ)
    (hAp : 1-a ≤ μ.real A) (hBp : 1-b ≤ μ.real B) :
    1-a-b ≤ μ.real (A ∩ B) := by
  have hh := measureReal_union_le (μ:=μ) Aᶜ Bᶜ
  rw [← Set.compl_inter,measureReal_compl (hA.inter hB),
    measureReal_compl hA,measureReal_compl hB,probReal_univ] at hh
  linarith

theorem ThresholdDecisionSafe.accepted_target_le (ell ε α : ℝ) (hα : 0 ≤ α)
    (hεα : 2*ε ≤ α) (d : ThresholdDecision) (hsafe : ThresholdDecisionSafe ell ε d)
    (haccept : d ≠ .below) : ell ≤ 1+α := by
  cases d with
  | below => exact False.elim (haccept rfl)
  | above => change ell < 1 at hsafe; linarith
  | near =>
    change |1-ell| ≤ 2*ε at hsafe
    have hh := (abs_le.mp hsafe).1
    linarith

theorem MainSketchGood.absolute_query_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) (t : {t : ℝ // 0 < t}) :
    ∃ E : Set (AbsoluteQuerySamples C.pair.dimension s I.repetitions × AbsoluteInertiaSamples C.pair.dimension I.repetitions),
      MeasurableSet E ∧
      ((repeatedGaussianColumns C.pair.dimension (s+1) I.repetitions).prod
        (absoluteInertiaLaw C.pair.dimension I.repetitions)).real E ≥ 1-I.queryFailure ∧
      ∀ z ∈ E, ThresholdDecisionSafe
        (orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
          (mainThresholdOperator_isHermitian I S C t.val _) ⟨s,hs⟩)
        (mainRitzAccuracy I) (absolutePositiveQueryProgram kernels I S C s hs t z.1 z.2).eval := by
  let base := mainStrongBase kernels I S C t
  let T := mainThresholdOperator I S C t.val base
  let source := mainSourceFactor I S C t.val base
  let Sinv := (mainRefinedFactor I S C t.val base)⁻¹*base.inverseFactor
  let a := (1+hierarchyUpper L/(8*I.accuracy 0))⁻¹
  let b := 1+hierarchyUpper 0/(8*I.accuracy L)
  let actions := fun w => (mainThresholdAction kernels I S C t.val base (s+1)).columnBlocks (by omega) w
  have hT : T.PosSemidef := (hg.actual_threshold_bounds kernels I S C t.val t.property).1
  have hc := hg.actual_source_condition kernels I S C t.val t.property
  have hstop : 10*gaussianCaptureRadius C.pair.dimension (mainConditionBound I) (1/2)/(mainRitzAccuracy I) ≤
      strongFilterDenominator (mainRitzAccuracy I/100) (absoluteKrylovDegree I S C (by omega)) :=
    krylovDegree_stops _ _ _ _ (by omega) (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
      (mainRitzAccuracy_positive I) (mainRitzAccuracy_le_one I)
  have hε : mainRitzAccuracy I ≤ 1/4 := by
    have hh := I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    unfold mainRitzAccuracy
    linarith
  obtain ⟨E,hEm,hEp,hE⟩ := repeatedKrylovQueryProgram_fixed_good_event kernels T hT actions source Sinv hc.1
    ⟨s,hs⟩ a b (mainConditionBound I) (1/2) (mainRitzAccuracy I)
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
    (by norm_num) (by norm_num) (mainRitzAccuracy_positive I) hε
    (absoluteKrylovDegree I S C (by omega)) hstop I.repetitions
    (mainSourceAction kernels I S C t.val base (s+1))
  refine ⟨E,hEm,?_,?_⟩
  · have hhalf : (1/2:ℝ)^I.repetitions ≤ I.queryFailure :=
      repetition_halving_cap I.queryFailure I.queryFailure_positive (1/2) (by norm_num) (by norm_num)
    linarith
  · intro z hz
    rw [absolutePositiveQueryProgram_eval_repeated]
    exact hE z hz

/-- Success data required by an accepted attempt. This is a conclusion of
an explicit event theorem, rather than an assumed output certificate. -/
def AbsoluteRankThresholdGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hs : s < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t}) (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) : Prop :=
  ThresholdDecisionSafe
    (orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨s,hs⟩)
    (mainRitzAccuracy I) (absolutePositiveQueryProgram kernels I S C s hs t z.1 z.2.1).eval ∧
  ((absolutePositiveQueryProgram kernels I S C s hs t z.1 z.2.1).eval ≠ .below →
    z.2.2 ∈ physicalStrongSuccess (supportLeftFactor I.A S.initialA C.pair)
      (mainRefinedFactor I S C t.val (mainStrongBase kernels I S C t)) (mainTruePencil I S C t.val)
      (absoluteStrongPhysicalPolynomial kernels I S C s hk t) I.alpha)

theorem MainSketchGood.absolute_rank_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t}) :
    ∃ E : Set (AbsoluteProbabilityTape C.pair.dimension s I.repetitions), MeasurableSet E ∧
      (absoluteProbabilityLaw C.pair.dimension s I.repetitions).real E ≥ 1-I.queryFailure-I.singleFailure ∧
      ∀ z ∈ E, AbsoluteRankThresholdGood kernels I S C s hs hk t z := by
  classical
  let target := orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
    (mainThresholdOperator_isHermitian I S C t.val _) ⟨s,hs⟩
  obtain ⟨EQ,hEQm,hEQp,hEQ⟩ := hg.absolute_query_good_event kernels I S C s hs t
  have hstrong : ∃ ES : Set (Fin s → Fin C.pair.dimension → ℝ), MeasurableSet ES ∧
      (gaussianColumns C.pair.dimension s).real ES ≥ 1-I.singleFailure ∧
      ∀ G ∈ ES, target ≤ 1+I.alpha →
        G ∈ physicalStrongSuccess (supportLeftFactor I.A S.initialA C.pair)
          (mainRefinedFactor I S C t.val (mainStrongBase kernels I S C t)) (mainTruePencil I S C t.val)
          (absoluteStrongPhysicalPolynomial kernels I S C s hk t) I.alpha := by
    by_cases ht : target ≤ 1+I.alpha
    · obtain ⟨ES,hESm,hESp,hES⟩ := hg.absolute_strong_physical_good_event kernels I S C s hs hk t ht
      exact ⟨ES,hESm,hESp,fun G hG _ => hES G hG⟩
    · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
      · simp only [probReal_univ]
        linarith [I.singleFailure_positive]
      · intro G _ htarget
        exact False.elim (ht htarget)
  obtain ⟨ES,hESm,hESp,hES⟩ := hstrong
  let qproj := fun z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions => (z.1,z.2.1)
  let sproj := fun z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions => z.2.2
  have hq : MeasurePreserving qproj (absoluteProbabilityLaw C.pair.dimension s I.repetitions)
      ((repeatedGaussianColumns C.pair.dimension (s+1) I.repetitions).prod
        (absoluteInertiaLaw C.pair.dimension I.repetitions)) := by
    have hp := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc
      (repeatedGaussianColumns C.pair.dimension (s+1) I.repetitions)
      (absoluteInertiaLaw C.pair.dimension I.repetitions) (gaussianColumns C.pair.dimension s))
    exact measurePreserving_fst.comp hp
  have hsproj : MeasurePreserving sproj (absoluteProbabilityLaw C.pair.dimension s I.repetitions)
      (gaussianColumns C.pair.dimension s) := measurePreserving_snd.comp measurePreserving_snd
  let E := (qproj ⁻¹' EQ) ∩ (sproj ⁻¹' ES)
  have hqm := hEQm.preimage hq.measurable
  have hsm := hESm.preimage hsproj.measurable
  refine ⟨E,hqm.inter hsm,?_,?_⟩
  · apply probability_inter_event _ _ _ hqm hsm I.queryFailure I.singleFailure
    · rw [hq.measureReal_preimage hEQm.nullMeasurableSet]
      exact hEQp
    · rw [hsproj.measureReal_preimage hESm.nullMeasurableSet]
      exact hESp
  · intro z hz
    have hsafe := hEQ (qproj z) hz.1
    refine ⟨hsafe,?_⟩
    intro haccept
    apply hES (sproj z) hz.2
    exact ThresholdDecisionSafe.accepted_target_le target (mainRitzAccuracy I) I.alpha
      I.alpha_positive.le (by unfold mainRitzAccuracy; linarith [I.alpha_positive]) _ hsafe haccept

end
end HierarchicalAbsoluteSpectral
