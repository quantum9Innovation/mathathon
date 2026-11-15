import HierarchicalAbsoluteSpectral.MainStatementsArrays
import HierarchicalAbsoluteSpectral.MainSketchProgram
import HierarchicalAbsoluteSpectral.ThresholdSelection

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

/-- The complete small-core pipeline. The support record and stored sketches
are produced by the preceding actual programs, not successful certificates. -/
def mainCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) : ArithmeticProgram (FixedRankOutput n p r) :=
  if hrank : C.pair.dimension ≤ r then
    supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hrank
  else do
    let initializer ← gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure
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
          (Nat.lt_of_not_ge hrank) t (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
          (Fin.cast hcap i)
      let result ← thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive query lower' upper'
      .branch result.selected 0 (fun _ => .pure (zeroFixedRankOutput n p r)) (fun ht =>
        mainStrongThresholdProgram kernels I S C (by omega) ⟨result.selected,lt_of_not_ge ht⟩
          (mainStrongArray I S C g))

theorem mainCoreProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) : (mainCoreProgram kernels I S C g).admissible := by
  unfold mainCoreProgram
  split_ifs with hrank
  · exact supportExactOutputProgram_admissible kernels I.A I.B _ hrank
  · have hk : 1 ≤ C.pair.dimension := by omega
    have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
    simp only [admissible_bind,gaussianInitializerProgram_admissible kernels _ _ _ hk hβ,true_and]
    split
    · exact exactPhysicalOutputProgram_admissible kernels I.A I.B _ _ _
    · simp only [admissible_bind,admissible_div,admissible_mul,certify_admissible,
        initializerRatioProgram_admissible m I.singleFailure hβ.ne',true_and,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
      constructor
      · apply thresholdSearchCapped_admissible_all
        intro i t
        apply positiveThresholdQuery_admissible
        intro number threshold
        exact mainPositiveQueryProgram_admissible kernels I S C _ threshold _ _
      · simp only [ArithmeticProgram.admissible]
        split_ifs
        exact mainStrongThresholdProgram_admissible kernels I S C hk _ _

/-- Original inputs, one fixed independent Gaussian tape, and the original
feasible arithmetic-kernel family determine the same executable program
used by the fixed-depth correctness and operation-count theorems. -/
def fixedDepthProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let sketches ← mainSketchProgram I g
  let support ← coarseSupportProgram kernels sketches.initialA sketches.initialB
  mainCoreProgram kernels I sketches support g

theorem fixedDepthProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (fixedDepthProgram kernels I g).admissible := by
  simp only [fixedDepthProgram,admissible_bind,mainSketchProgram_admissible,
    coarseSupportProgram_admissible,mainCoreProgram_admissible,and_self]

theorem fixedDepthProgram_rank_cap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (fixedDepthProgram kernels I g).eval.width ≤ r ∧
      (fixedDepthProgram kernels I g).eval.product.rank ≤ r :=
  ⟨(fixedDepthProgram kernels I g).eval.width_le,(fixedDepthProgram kernels I g).eval.rank_le⟩

end
end HierarchicalAbsoluteSpectral
