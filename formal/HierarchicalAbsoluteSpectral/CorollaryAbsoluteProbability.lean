import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityAssembly

/-! The fixed absolute threshold and every possible attempted rank share one
measurable success event under the literal absolute algorithm's Gaussian law.
No strong output or query correctness certificate is assumed in this result. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p L : ℕ}

/-- Pointwise query and carried-filter guarantees for all attempted ranks,
including zero, on the one fixed absolute threshold. -/
def AbsoluteCoreThresholdGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (z : AbsoluteCoreTape I) : Prop :=
  ∀ (s : Fin (m+1)) (hs : s.val < C.pair.dimension),
    AbsoluteRankThresholdGood kernels I.seed S C s.val hs (by omega)
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
      (absoluteProbabilityTapeRestriction C.pair.dimension_le_fin (z s))

theorem AbsoluteProblem.queryFailure_le_singleFailure (I : AbsoluteProblem n m p L) :
    I.seed.queryFailure ≤ I.seed.singleFailure := by
  unfold FixedProblem.queryFailure FixedProblem.singleFailure
  apply div_le_div_of_nonneg_left I.seed.delta_positive.le (by norm_num)
  have hc : (0:ℝ) ≤ I.seed.queryCap := Nat.cast_nonneg _
  nlinarith

theorem AbsoluteProblem.absolute_event_failure_budget (I : AbsoluteProblem n m p L) :
    I.seed.delta/10+((m:ℝ)+1)*(I.seed.queryFailure+I.seed.singleFailure) ≤ I.delta := by
  have hq := I.queryFailure_le_singleFailure
  have hm : 0 < (m:ℝ)+1 := by positivity
  have hseed : ((m:ℝ)+1)*I.seed.delta = I.delta := by
    change ((m:ℝ)+1)*(I.delta/((m:ℝ)+1))=I.delta
    field_simp [hm.ne']
  have hbound : ((m:ℝ)+1)*(I.seed.queryFailure+I.seed.singleFailure) ≤ I.delta/10 := by
    have hh := mul_le_mul_of_nonneg_left (show I.seed.queryFailure+I.seed.singleFailure ≤
      I.seed.delta/10 by unfold FixedProblem.singleFailure at *; linarith) hm.le
    nlinarith
  have hsmall : I.seed.delta ≤ I.delta := by
    change I.delta/((m:ℝ)+1) ≤ I.delta
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_nonneg I.delta_positive.le (Nat.cast_nonneg m)]
  linarith [I.delta_positive]

/-- Original input data, the exact sketch/support programs, fresh arrays
allocated by rank, and the fixed tolerance determine a measurable common
event of probability at least `1-delta`. -/
theorem absolute_fixed_threshold_all_ranks_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) :
    ∃ E : Set (AbsoluteTape I), MeasurableSet E ∧
      (absoluteRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let S := (mainSketchProgram I.seed g.1).eval
        let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
        MainSketchGood I.seed S ∧ AbsoluteCoreThresholdGood kernels I S C g.2 := by
  classical
  let β := ((m:ℝ)+1)*(I.seed.queryFailure+I.seed.singleFailure)
  have hβ : 0 ≤ β := mul_nonneg (by positivity)
    (add_nonneg I.seed.queryFailure_positive.le I.seed.singleFailure_positive.le)
  let support := fun z : MainSketchSampleTape I.seed =>
    (coarseSupportProgram kernels (mainSketchFromFiniteSample I.seed z).initialA
      (mainSketchFromFiniteSample I.seed z).initialB).eval
  have hf (z : MainSketchSampleTape I.seed) :
      ∃ F : Set (AbsoluteCoreTape I), MeasurableSet F ∧
        (absoluteCoreLaw I).real F ≥ 1-β ∧ ∀ g ∈ F,
          MainSketchGood I.seed (mainSketchFromFiniteSample I.seed z) →
            AbsoluteCoreThresholdGood kernels I (mainSketchFromFiniteSample I.seed z) (support z) g := by
    by_cases hz : MainSketchGood I.seed (mainSketchFromFiniteSample I.seed z)
    · obtain ⟨F,hFm,hFp,hF⟩ := hz.absolute_all_ranks_good_event kernels I.seed
        (mainSketchFromFiniteSample I.seed z) (support z)
        ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
      exact ⟨F,hFm,hFp,fun g hg _ => hF g hg⟩
    · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
      · simp only [probReal_univ]
        linarith
      · intro g _ hgood
        exact False.elim (hz hgood)
  choose F hFm hFp hF using hf
  have hh := absolute_random_finite_core_success I F β hβ
    (fun z _ => hFm z) (fun z _ => hFp z)
  let E := {g : AbsoluteTape I | MainSketchGood I.seed (mainSketchProgram I.seed g.1).eval ∧
    g.2 ∈ F (mainSketchFiniteSample I.seed g.1)}
  refine ⟨E,hh.1,?_,?_⟩
  · have hb := I.absolute_event_failure_budget
    change _ ≤ (absoluteRandomLaw I).real E
    linarith [hh.2]
  · intro g hg
    have hgood := hg.1
    refine ⟨hgood,?_⟩
    rw [mainSketchProgram_factorization] at hgood ⊢
    exact hF (mainSketchFiniteSample I.seed g.1) g.2 hg.2 hgood

end
end HierarchicalAbsoluteSpectral
