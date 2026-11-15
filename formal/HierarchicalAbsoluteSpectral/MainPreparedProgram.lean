import HierarchicalAbsoluteSpectral.MainOperatorPreparedCore
import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm

/-! The main arithmetic program consumes its computed tolerances, hierarchy
ratios and repetition count. The exact baseline program equality transports
all correctness and work theorems without changing the randomized output. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def mainPreparedSketchProgram (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (g : MainRandomTape I) : ArithmeticProgram (StoredSketches n m p L) := do
  let SA ← finiteTabulateProgram (fun j : Fin (L+1) => boundedSketchProgram I.A
    (I.accuracy j.val) P.sketchFailure.val (I.accuracy_positive j.val (by omega))
      (by rw [P.sketchFailure.property]; exact mainSketchFailure_positive I) (mainLeftSketchInput I g j))
  let SB ← finiteTabulateProgram (fun j : Fin (L+1) => boundedSketchProgram I.Bᵀ
    (I.accuracy j.val) P.sketchFailure.val (I.accuracy_positive j.val (by omega))
      (by rw [P.sketchFailure.property]; exact mainSketchFailure_positive I) (mainRightSketchInput I g j))
  ArithmeticProgram.pure
    { levelA := fun j => ⟨(SA j).rows,(SA j).value⟩
      levelB := fun j => ⟨(SB j).rows,(SB j).value⟩
      rowsA := fun j => (SA j).rows_le
      rowsB := fun j => (SB j).rows_le }

theorem mainPreparedSketchProgram_eq (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (g : MainRandomTape I) : mainPreparedSketchProgram I P g=mainSketchProgram I g := by
  rw [P.eq_canonical I]
  rfl

def mainPreparedPositiveQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  let ε ← (div P.alpha.val 100).certify
  have hε : ε.val=I.alpha/100 := by rw [ε.property,eval_div,P.alpha.property]
  let actions := fun b => (mainPreparedThresholdAction kernels I P S C t.val base (r+1)).columnBlocks (by omega) b
  automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
    (mainThresholdOperator_isHermitian I S C t.val base) actions
    (mainSourceFactor I S C t.val base) (mainPreparedSourceAction kernels I P S C t.val base (r+1))
    ⟨r,hr⟩ bound.val ε.val (by omega)
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [hε]; exact div_pos I.alpha_positive (by norm_num))
    (by rw [hε]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    P.repetitions.val
    (fun j => G (Fin.cast P.repetitions.property j))
    (fun j => g (Fin.cast P.repetitions.property j))

theorem mainPreparedPositiveQueryProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    mainPreparedPositiveQueryProgram kernels I P S C hr t G g=
      mainPositiveQueryProgram kernels I S C hr t G g := by
  rw [PreparedMainScalars.eq_canonical I P]
  simp only [mainPreparedPositiveQueryProgram,canonicalMainScalars,
    mainPreparedThresholdAction_eq,mainPreparedSourceAction_eq,Fin.cast_refl]
  rfl

def mainPreparedStrongThresholdProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) : ArithmeticProgram (FixedRankOutput n p r) := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  strongProjectionOutputProgram kernels I.A I.B
    (mainPreparedCarriedAction kernels I P S C t.val base r)
    (mainPreparedPhysicalMapAction kernels I P S C t.val base r)
    bound.val P.singleFailure.val P.alpha.val hk
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [P.singleFailure.property]; exact div_pos I.delta_positive (by norm_num))
    (by rw [P.singleFailure.property]; have := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    (by rw [P.alpha.property]; exact I.alpha_positive)
    (by rw [P.alpha.property]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    (columnsMatrix G)

theorem mainPreparedStrongThresholdProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    mainPreparedStrongThresholdProgram kernels I P S C hk t G=
      mainStrongThresholdProgram kernels I S C hk t G := by
  rw [PreparedMainScalars.eq_canonical I P]
  simp only [mainPreparedStrongThresholdProgram,canonicalMainScalars,
    mainPreparedCarriedAction_eq,mainPreparedPhysicalMapAction_eq]
  rfl

def mainPreparedCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) : ArithmeticProgram (FixedRankOutput n p r) :=
  if hrank : C.pair.dimension ≤ r then
    supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hrank
  else do
    let initializer ← gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) P.singleFailure.val
    match initializer.result with
    | .exact =>
      exactPhysicalOutputProgram kernels I.A I.B
        (mainSupportAction kernels I S C initializer.range.dimension) initializer.range.basis
        initializer.range.dimension_le_cols
    | .bracket lower upper => do
      let lower' ← div lower 4
      let upper' ← mul 4 upper
      let ratio ← (initializerRatioProgram m P.singleFailure.val).certify
      let budget ← (mul 16 ratio.val).certify
      have hbudget : budget.val=16*initializerRatio m I.singleFailure := by
        rw [budget.property,eval_mul,ratio.property,initializerRatioProgram_eval,P.singleFailure.property]
      have hnear : 0 < P.near.val := by rw [P.near.property]; exact I.nearTolerance_positive
      have hcap : leastHalvings budget.val P.near.val hnear=I.queryCap := by
        rw [hbudget]
        simp only [P.near.property]
        rfl
      let query := fun i : Fin (leastHalvings budget.val P.near.val hnear) =>
        positiveThresholdQuery (fun number t => mainPreparedPositiveQueryProgram kernels I P S C
          (Nat.lt_of_not_ge hrank) t (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
          (Fin.cast hcap i)
      let result ← thresholdSearchCapped budget.val P.near.val hnear query lower' upper'
      .branch result.selected 0 (fun _ => .pure (zeroFixedRankOutput n p r)) (fun ht =>
        mainPreparedStrongThresholdProgram kernels I P S C (by omega) ⟨result.selected,lt_of_not_ge ht⟩
          (mainStrongArray I S C g))

theorem mainPreparedCoreProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (g : MainRandomTape I) :
    mainPreparedCoreProgram kernels I P S C g=mainCoreProgram kernels I S C g := by
  rw [PreparedMainScalars.eq_canonical I P]
  simp only [mainPreparedCoreProgram,mainCoreProgram,canonicalMainScalars,
    mainPreparedPositiveQueryProgram_eq,mainPreparedStrongThresholdProgram_eq]
  rfl

def preparedMainCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let parameters ← mainScalarProgram I
  mainPreparedCoreProgram kernels I parameters S C g

theorem preparedMainCoreProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) :
    (preparedMainCoreProgram kernels I S C g).eval=(mainCoreProgram kernels I S C g).eval := by
  simp only [preparedMainCoreProgram,eval_bind,mainPreparedCoreProgram_eq]

theorem preparedMainCoreProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) :
    (preparedMainCoreProgram kernels I S C g).work=
      4*L+3*I.queryCap+2*I.repetitions+29+(mainCoreProgram kernels I S C g).work := by
  simp only [preparedMainCoreProgram,work_bind,mainScalarProgram_work,mainPreparedCoreProgram_eq]

theorem preparedMainCoreProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) :
    (preparedMainCoreProgram kernels I S C g).admissible := by
  simp only [preparedMainCoreProgram,admissible_bind,mainScalarProgram_admissible,
    mainPreparedCoreProgram_eq,mainCoreProgram_admissible,and_self]

def mainPreparedPipelineProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let sketches ← mainPreparedSketchProgram I P g
  let support ← coarseSupportProgram kernels sketches.initialA sketches.initialB
  mainPreparedCoreProgram kernels I P sketches support g

theorem mainPreparedPipelineProgram_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I) (g : MainRandomTape I) :
    mainPreparedPipelineProgram kernels I P g=fixedDepthProgram kernels I g := by
  simp only [mainPreparedPipelineProgram,fixedDepthProgram,mainPreparedSketchProgram_eq,mainPreparedCoreProgram_eq]

/-- Complete counted main program, including the derivation of every
input-dependent scalar tolerance and every data-dependent repetition count. -/
def preparedFixedDepthProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let parameters ← mainScalarProgram I
  mainPreparedPipelineProgram kernels I parameters g

theorem preparedFixedDepthProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthProgram kernels I g).eval=(fixedDepthProgram kernels I g).eval := by
  simp only [preparedFixedDepthProgram,eval_bind,mainPreparedPipelineProgram_eq]

theorem preparedFixedDepthProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthProgram kernels I g).work=
      4*L+3*I.queryCap+2*I.repetitions+29+(fixedDepthProgram kernels I g).work := by
  simp only [preparedFixedDepthProgram,work_bind,mainScalarProgram_work,mainPreparedPipelineProgram_eq]

theorem preparedFixedDepthProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthProgram kernels I g).admissible := by
  simp only [preparedFixedDepthProgram,admissible_bind,mainScalarProgram_admissible,
    mainPreparedPipelineProgram_eq,fixedDepthProgram_admissible,and_self]

theorem preparedFixedDepthProgram_rank_cap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthProgram kernels I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram kernels I g).eval.product.rank ≤ r := by
  rw [preparedFixedDepthProgram_eval]
  exact fixedDepthProgram_rank_cap kernels I g

end
end HierarchicalAbsoluteSpectral
