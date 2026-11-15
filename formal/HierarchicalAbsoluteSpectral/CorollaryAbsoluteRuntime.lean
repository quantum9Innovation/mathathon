import HierarchicalAbsoluteSpectral.CorollaryAbsoluteCost
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteDraws
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteCorrectness
import HierarchicalAbsoluteSpectral.BaseMainTotalCost
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbability

/-! Finite all-outcome caps and the sharper cap on the very same success
event. Unused rank arrays are not charged as Gaussian samples. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p L : ℕ}

def absoluteUniformAttemptWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (R : ℕ) (Ck p0 : ℝ) : ℕ :=
  Finset.univ.sup (fun s : Fin (R+1) => absoluteAttemptWorkCap kernels I.seed S C s.val Ck p0+
    I.seed.repetitions*((s.val+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s.val*C.pair.dimension)

theorem absoluteUniformAttemptWorkCap_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (R s : ℕ) (hs : s ≤ R) (Ck p0 : ℝ) :
    absoluteAttemptWorkCap kernels I.seed S C s Ck p0+
      I.seed.repetitions*((s+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s*C.pair.dimension ≤
        absoluteUniformAttemptWorkCap kernels I S C R Ck p0 :=
  Finset.le_sup (f := fun s : Fin (R+1) => absoluteAttemptWorkCap kernels I.seed S C s.val Ck p0+
    I.seed.repetitions*((s.val+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s.val*C.pair.dimension)
      (Finset.mem_univ (⟨s,by omega⟩ : Fin (R+1)))

theorem absoluteCoreProgram_small_accounted_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (z : AbsoluteCoreTape I)
    (hsmall : 2*I.slackRank < m) :
    (absoluteCoreProgram kernels I S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).work+
      absoluteCoreGaussianDrawCount kernels I S C z ≤
        (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I S C (2*I.slackRank) Ck p0 := by
  apply absoluteDoublingLoop_small_accounted_work
  · intro s hslack hsm
    rw [dif_pos hsm.le]
    apply absoluteAttemptProgram_not_none
    intro hs
    exact hg.absolute_query_no_false_advance kernels I.seed S C s hs
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ _ _
      (hg.absolute_threshold_target_le_one kernels I S C s hs hslack)
  · exact hsmall
  · intro s hs
    have hsm : s ≤ m := by omega
    rw [dif_pos hsm,dif_pos hsm]
    have hw := absoluteAttemptProgram_work_bound kernels Ck p0 hC hp hK I.seed S C s
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    have hg := absoluteAttemptGaussianDrawCount_le kernels I.seed S C s
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    exact (Nat.add_le_add hw hg).trans (by
      simpa only [Nat.add_assoc] using absoluteUniformAttemptWorkCap_le kernels I S C (2*I.slackRank) s hs Ck p0)
  · exact Nat.zero_le _
  · simpa only [Nat.zero_add,absoluteRankAt_succ] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) m).le

theorem absoluteCoreProgram_all_outcome_accounted_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (z : AbsoluteCoreTape I) :
    (absoluteCoreProgram kernels I S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).work+
      absoluteCoreGaussianDrawCount kernels I S C z ≤
        (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I S C m Ck p0+(kernels n m p).cost := by
  rw [← absoluteFullProductProgram_work kernels I.A I.B]
  apply absoluteDoublingLoop_accounted_work_cap
  intro s hsm
  rw [dif_pos hsm.le,dif_pos hsm.le]
  have hw := absoluteAttemptProgram_work_bound kernels Ck p0 hC hp hK I.seed S C s
    ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
    (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
  have hg := absoluteAttemptGaussianDrawCount_le kernels I.seed S C s
    ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
    (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
  exact (Nat.add_le_add hw hg).trans (by
    simpa only [Nat.add_assoc] using absoluteUniformAttemptWorkCap_le kernels I S C m s hsm.le Ck p0)

theorem absolute_small_slack_strict_core (m s : ℕ) (hm : 1 ≤ m)
    (hs : s ≤ Nat.sqrt m/2) : 2*s < m := by
  have htwice : 2*s ≤ Nat.sqrt m := by omega
  by_cases hm1 : m=1
  · subst m
    norm_num at hs
    omega
  · have hm2 : 2 ≤ m := by omega
    exact htwice.trans_lt (Nat.sqrt_lt_self (by omega))

theorem absoluteAlgorithmProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    let S := (mainSketchProgram I.seed g.1).eval
    let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
    (absoluteAlgorithmProgram kernels I g).work=4+(mainSketchProgram I.seed g.1).work+
      (coarseSupportProgram kernels S.initialA S.initialB).work+
      (absoluteCoreProgram kernels I S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ g.2).work := by
  have ht : (absoluteThresholdProgram I).certify.eval=
      ⟨absoluteThreshold I,(absoluteThresholdProgram_eval I).symm⟩ :=
    Subtype.ext ((certify_eval _).trans (absoluteThresholdProgram_eval I))
  unfold absoluteAlgorithmProgram
  simp only [work_bind,certify_work,absoluteThresholdProgram_work]
  erw [ht]
  omega

def absolutePreprocessingWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) : ℕ :=
  4+(L+1)*(sketchFormationCap n m I.seed.sketchFailure+sketchFormationCap p m I.seed.sketchFailure)+
    coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
    absoluteSharedSketchGaussianDrawCount n p L+n*p

def absoluteSmallRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) (Ck p0 : ℝ) : ℕ :=
  let S := (mainSketchProgram I.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  4*L+3*I.seed.queryCap+2*I.seed.repetitions+31+absolutePreprocessingWorkCap kernels I S+
    (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I S C (2*I.slackRank) Ck p0

def absoluteAllOutcomeRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) (Ck p0 : ℝ) : ℕ :=
  let S := (mainSketchProgram I.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  4*L+3*I.seed.queryCap+2*I.seed.repetitions+31+absolutePreprocessingWorkCap kernels I S+
    (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I S C m Ck p0+(kernels n m p).cost

theorem preparedAbsoluteRandomizedWork_small_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I)
    (hsketch : MainSketchGood I.seed (mainSketchProgram I.seed g.1).eval)
    (hsmall : I.slackRank ≤ Nat.sqrt m/2) :
    preparedAbsoluteRandomizedWork kernels I g ≤ absoluteSmallRealizedWorkCap kernels I g Ck p0 := by
  let S := (mainSketchProgram I.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I.seed g.1
  have hc := coarseSupportProgram_work_bound kernels S.initialA S.initialB I.core_positive
  have hm := absoluteCoreProgram_small_accounted_work kernels Ck p0 hC hp hK I S hsketch C g.2
    (absolute_small_slack_strict_core m I.slackRank I.core_positive hsmall)
  rw [preparedAbsoluteRandomizedWork_eq,absoluteRandomizedWork,absoluteAlgorithmProgram_work]
  dsimp only [absoluteAlgorithmGaussianDrawCount,absoluteSmallRealizedWorkCap,absolutePreprocessingWorkCap]
  dsimp only [S,C] at hc hm
  omega

theorem preparedAbsoluteRandomizedWork_all_outcome_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    preparedAbsoluteRandomizedWork kernels I g ≤ absoluteAllOutcomeRealizedWorkCap kernels I g Ck p0 := by
  let S := (mainSketchProgram I.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I.seed g.1
  have hc := coarseSupportProgram_work_bound kernels S.initialA S.initialB I.core_positive
  have hm := absoluteCoreProgram_all_outcome_accounted_cap kernels Ck p0 hC hp hK I S C g.2
  rw [preparedAbsoluteRandomizedWork_eq,absoluteRandomizedWork,absoluteAlgorithmProgram_work]
  dsimp only [absoluteAlgorithmGaussianDrawCount,absoluteAllOutcomeRealizedWorkCap,absolutePreprocessingWorkCap]
  dsimp only [S,C] at hc hm
  omega

/-- One explicitly constructed event gives the error, the width bound and
the adaptive work bound together. The separate preceding theorem caps every
other outcome by the executed fallback and finite per-attempt bounds. -/
theorem absolute_error_width_and_runtime_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (I : AbsoluteProblem n m p L) :
    ∃ E : Set (AbsoluteTape I), MeasurableSet E ∧
      (absoluteRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (preparedAbsoluteAlgorithmProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance ∧
          (I.slackRank ≤ Nat.sqrt m/2 →
            preparedAbsoluteRandomizedWork kernels I g ≤ absoluteSmallRealizedWorkCap kernels I g Ck p0) := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_fixed_threshold_all_ranks_good_event kernels I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  obtain ⟨hsketch,hgood⟩ := hE g hg
  have hcorrect := absoluteCoreProgram_correct kernels I _ hsketch _ g.2 hgood
  rw [preparedAbsoluteAlgorithmProgram_eval,absoluteAlgorithmProgram_eval]
  exact ⟨hcorrect.1,hcorrect.2,
    fun hs => preparedAbsoluteRandomizedWork_small_bound kernels Ck p0 hC hp hK I g hsketch hs⟩

end
end HierarchicalAbsoluteSpectral
