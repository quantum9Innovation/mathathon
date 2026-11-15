import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm
import HierarchicalAbsoluteSpectral.ProbabilityMainTapeLaw

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def mainCoreProgramFromArrays (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (initial : Fin r → Fin C.pair.dimension → ℝ)
    (queries : Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (inertias : Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (strong : Fin r → Fin C.pair.dimension → ℝ) : ArithmeticProgram (FixedRankOutput n p r) :=
  if hrank : C.pair.dimension ≤ r then
    supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hrank
  else do
    let initializer ← gaussianInitializerProgram kernels C.rightGram (columnsMatrix initial) I.singleFailure
    match initializer.result with
    | .exact =>
      exactPhysicalOutputProgram kernels I.A I.B
        (mainSupportAction kernels I S C initializer.range.dimension) initializer.range.basis
        initializer.range.dimension_le_cols
    | .bracket lower upper => do
      let lower' ← div lower 4
      let upper' ← mul 4 upper
      let ratio ← (initializerRatioProgram m I.singleFailure).certify
      let budget ← (mul 16 ratio.val).certify
      have hbudget : budget.val=16*initializerRatio m I.singleFailure := by
        rw [budget.property,eval_mul,ratio.property,initializerRatioProgram_eval]
      have hcap : leastHalvings budget.val I.nearTolerance I.nearTolerance_positive=I.queryCap := by
        rw [hbudget]
        rfl
      let query := fun i : Fin (leastHalvings budget.val I.nearTolerance I.nearTolerance_positive) =>
        positiveThresholdQuery (fun number t => mainPositiveQueryProgram kernels I S C
          (Nat.lt_of_not_ge hrank) t (queries number) (inertias number)) (Fin.cast hcap i)
      let result ← thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive query lower' upper'
      .branch result.selected 0 (fun _ => .pure (zeroFixedRankOutput n p r)) (fun ht =>
        mainStrongThresholdProgram kernels I S C (by omega) ⟨result.selected,lt_of_not_ge ht⟩ strong)

theorem mainCoreProgram_eq_fromArrays (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) :
    mainCoreProgram kernels I S C g = mainCoreProgramFromArrays kernels I S C
      (mainInitializerArray I S C g) (mainQueryArray I S C g) (mainInertiaArray I S C g) (mainStrongArray I S C g) := rfl

theorem mainCoreProgram_congr_arrays (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g h : MainRandomTape I)
    (hi : mainInitializerArray I S C g=mainInitializerArray I S C h)
    (hq : mainQueryArray I S C g=mainQueryArray I S C h)
    (hd : mainInertiaArray I S C g=mainInertiaArray I S C h)
    (hs : mainStrongArray I S C g=mainStrongArray I S C h) :
    mainCoreProgram kernels I S C g=mainCoreProgram kernels I S C h := by
  rw [mainCoreProgram_eq_fromArrays,mainCoreProgram_eq_fromArrays,hi,hq,hd,hs]

def mainCoreTapeExtend (I : FixedProblem n m p r L) (c : MainCoreTapeOriginal I) : MainRandomTape I
  | .sketchLeft _ _ _ => 0
  | .sketchRight _ _ _ => 0
  | .initializer j i => c.1 j i
  | .query q u j i => c.2.1 q u j i
  | .inertia q u t i => c.2.2.1 q u t i
  | .strong j i => c.2.2.2 j i

theorem mainCoreTapeExtend_original (I : FixedProblem n m p r L) (c : MainCoreTapeOriginal I) :
    mainCoreTapeOriginal I (mainCoreTapeExtend I c)=c := by
  rcases c with ⟨a,b,d,s⟩
  rfl

theorem mainCoreProgram_factorization (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) : mainCoreProgram kernels I S C g =
      mainCoreProgram kernels I S C (mainCoreTapeExtend I (mainCoreTapeOriginal I g)) := by
  apply mainCoreProgram_congr_arrays <;> rfl

def mainCoreProgramFromOriginalTape (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (c : MainCoreTapeOriginal I) : ArithmeticProgram (FixedRankOutput n p r) :=
  mainCoreProgram kernels I S C (mainCoreTapeExtend I c)

def mainProgramFromFiniteStateCoreTape (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (z : MainSketchSampleTape I) (c : MainCoreTapeOriginal I) :
    FixedRankOutput n p r :=
  let S := mainSketchFromFiniteSample I z
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  (mainCoreProgramFromOriginalTape kernels I S C c).eval

theorem fixedDepthProgram_eval_factorization (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (fixedDepthProgram kernels I g).eval = mainProgramFromFiniteStateCoreTape kernels I
      (mainSketchFiniteSample I g) (mainCoreTapeOriginal I g) := by
  unfold fixedDepthProgram
  rw [eval_bind,eval_bind,mainSketchProgram_factorization]
  exact congrArg ArithmeticProgram.eval (mainCoreProgram_factorization kernels I _ _ g)

end
end HierarchicalAbsoluteSpectral
