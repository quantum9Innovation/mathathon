import HierarchicalAbsoluteSpectral.CorollaryAbsoluteAlgorithm
import HierarchicalAbsoluteSpectral.MainPreparedProgram

/-! The absolute controller consumes the actual computed scalar table. The
baseline program equality transports its exact output and branch behavior. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def absolutePreparedPositiveQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hr : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  let ε ← (div P.alpha.val 100).certify
  have hε : ε.val=I.alpha/100 := by rw [ε.property,eval_div,P.alpha.property]
  let actions := fun b => (mainPreparedThresholdAction kernels I P S C t.val base (s+1)).columnBlocks (by omega) b
  automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
    (mainThresholdOperator_isHermitian I S C t.val base) actions
    (mainSourceFactor I S C t.val base) (mainPreparedSourceAction kernels I P S C t.val base (s+1))
    ⟨s,hr⟩ bound.val ε.val (by omega)
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [hε]; exact div_pos I.alpha_positive (by norm_num))
    (by rw [hε]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    P.repetitions.val
    (fun j => G (Fin.cast P.repetitions.property j))
    (fun j => g (Fin.cast P.repetitions.property j))

theorem absolutePreparedPositiveQueryProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hr : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    absolutePreparedPositiveQueryProgram kernels I P S C s hr t G g=
      absolutePositiveQueryProgram kernels I S C s hr t G g := by
  rw [PreparedMainScalars.eq_canonical I P]
  simp only [absolutePreparedPositiveQueryProgram,canonicalMainScalars,
    mainPreparedThresholdAction_eq,mainPreparedSourceAction_eq,Fin.cast_refl]
  rfl

def absolutePreparedStrongThresholdProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) : ArithmeticProgram (FixedRankOutput n p s) := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  strongProjectionOutputProgram kernels I.A I.B
    (mainPreparedCarriedAction kernels I P S C t.val base s)
    (mainPreparedPhysicalMapAction kernels I P S C t.val base s)
    bound.val P.singleFailure.val P.alpha.val hk
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [P.singleFailure.property]; exact div_pos I.delta_positive (by norm_num))
    (by rw [P.singleFailure.property]; have := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    (by rw [P.alpha.property]; exact I.alpha_positive)
    (by rw [P.alpha.property]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    (columnsMatrix G)

theorem absolutePreparedStrongThresholdProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    absolutePreparedStrongThresholdProgram kernels I P S C s hk t G=
      absoluteStrongThresholdProgram kernels I S C s hk t G := by
  rw [PreparedMainScalars.eq_canonical I P]
  simp only [absolutePreparedStrongThresholdProgram,canonicalMainScalars,
    mainPreparedCarriedAction_eq,mainPreparedPhysicalMapAction_eq]
  rfl


def absolutePreparedAttemptProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    ArithmeticProgram (Option (FixedRankOutput n p s)) :=
  if hrank : C.pair.dimension ≤ s then do
    let out ← supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hrank
    .pure (some out)
  else do
    let decision ← absolutePreparedPositiveQueryProgram kernels I P S C s (Nat.lt_of_not_ge hrank) t z.1 z.2.1
    match decision with
    | .below => .pure none
    | .above | .near => do
      let out ← absolutePreparedStrongThresholdProgram kernels I P S C s (by omega) t z.2.2
      .pure (some out)

theorem absolutePreparedAttemptProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    absolutePreparedAttemptProgram kernels I P S C s t z=absoluteAttemptProgram kernels I S C s t z := by
  simp only [absolutePreparedAttemptProgram,absoluteAttemptProgram,
    absolutePreparedPositiveQueryProgram_eq,absolutePreparedStrongThresholdProgram_eq]
  rfl

def absolutePreparedCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (P : PreparedMainScalars I.seed)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) (z : AbsoluteCoreTape I) : ArithmeticProgram (AbsoluteOutput n p m) :=
  absoluteDoublingProgram (fun s =>
    if hs : s ≤ m then absolutePreparedAttemptProgram kernels I.seed P S C s t
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    else .pure none) (absoluteFullProductProgram kernels I.A I.B)

theorem absolutePreparedCoreProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (P : PreparedMainScalars I.seed)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) (z : AbsoluteCoreTape I) :
    absolutePreparedCoreProgram kernels I P S C t z=absoluteCoreProgram kernels I S C t z := by
  simp only [absolutePreparedCoreProgram,absoluteCoreProgram,absolutePreparedAttemptProgram_eq]

def absolutePreparedPipelineProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (P : PreparedMainScalars I.seed) (g : AbsoluteTape I) :
    ArithmeticProgram (AbsoluteOutput n p m) := do
  let t ← (absoluteThresholdProgram I).certify
  have ht : 0 < t.val := by rw [t.property,absoluteThresholdProgram_eval]; exact absoluteThreshold_positive I
  let sketches ← mainPreparedSketchProgram I.seed P g.1
  let support ← coarseSupportProgram kernels sketches.initialA sketches.initialB
  absolutePreparedCoreProgram kernels I P sketches support ⟨t.val,ht⟩ g.2

theorem absolutePreparedPipelineProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (P : PreparedMainScalars I.seed) (g : AbsoluteTape I) :
    absolutePreparedPipelineProgram kernels I P g=absoluteAlgorithmProgram kernels I g := by
  simp only [absolutePreparedPipelineProgram,absoluteAlgorithmProgram,
    mainPreparedSketchProgram_eq,absolutePreparedCoreProgram_eq]

/-- The allocated failure probability is computed before deriving the
hierarchy scalar table; its exact equality merely transports that table. -/
def absolutePreparationProgram (I : AbsoluteProblem n m p L) : ArithmeticProgram (PreparedMainScalars I.seed) := do
  let denominator ← (add (m:ℝ) 1).certify
  let failure ← certifyAs (div I.delta denominator.val) I.seed.delta (by
    rw [eval_div,denominator.property,eval_add]; rfl)
  let J : FixedProblem n m p 1 L :=
    { I.seed with delta := failure.val
                  delta_positive := by rw [failure.property]; exact I.seed.delta_positive
                  delta_lt_one := by rw [failure.property]; exact I.seed.delta_lt_one }
  have hJ : J=I.seed := by simp only [J,failure.property]
  let P ← mainScalarProgram J
  .pure (hJ ▸ P)

theorem absolutePreparationProgram_eval (I : AbsoluteProblem n m p L) :
    (absolutePreparationProgram I).eval=canonicalMainScalars I.seed :=
  PreparedMainScalars.eq_canonical I.seed _

theorem absolutePreparationProgram_admissible (I : AbsoluteProblem n m p L) :
    (absolutePreparationProgram I).admissible := by
  unfold absolutePreparationProgram
  simp only [admissible_bind,certify_admissible,admissible_add,certifyAs_admissible,
    admissible_div,certify_eval,eval_add,certifyAs_eval,mainScalarProgram_admissible,
    admissible_pure,and_true,true_and]
  positivity

theorem absolutePreparationProgram_work (I : AbsoluteProblem n m p L) :
    (absolutePreparationProgram I).work=4*L+3*I.seed.queryCap+2*I.seed.repetitions+31 := by
  unfold absolutePreparationProgram
  simp only [work_bind,certify_work,work_add,certifyAs_work,work_div,certifyAs_eval,
    mainScalarProgram_work,work_pure,Nat.add_zero]
  change 1+(1+(4*L+3*I.seed.queryCap+2*I.seed.repetitions+29)) = _
  omega

def preparedAbsoluteAlgorithmProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ArithmeticProgram (AbsoluteOutput n p m) := do
  let P ← absolutePreparationProgram I
  absolutePreparedPipelineProgram kernels I P g

theorem preparedAbsoluteAlgorithmProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    (preparedAbsoluteAlgorithmProgram kernels I g).eval=(absoluteAlgorithmProgram kernels I g).eval := by
  simp only [preparedAbsoluteAlgorithmProgram,eval_bind,absolutePreparedPipelineProgram_eq]

theorem preparedAbsoluteAlgorithmProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    (preparedAbsoluteAlgorithmProgram kernels I g).admissible := by
  simp only [preparedAbsoluteAlgorithmProgram,admissible_bind,absolutePreparationProgram_admissible,
    absolutePreparedPipelineProgram_eq,absoluteAlgorithmProgram_admissible,and_self]

theorem preparedAbsoluteAlgorithmProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    (preparedAbsoluteAlgorithmProgram kernels I g).work=
      4*L+3*I.seed.queryCap+2*I.seed.repetitions+31+(absoluteAlgorithmProgram kernels I g).work := by
  simp only [preparedAbsoluteAlgorithmProgram,work_bind,absolutePreparationProgram_work,
    absolutePreparedPipelineProgram_eq]

end
end HierarchicalAbsoluteSpectral
