import HierarchicalAbsoluteSpectral.BaseMainStrongCost
import HierarchicalAbsoluteSpectral.BaseMainSearchCost
import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}
attribute [local irreducible] mainPositiveQueryProgram mainStrongThresholdProgram
  gaussianInitializerProgram thresholdSearchCapped

def mainBracketProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ) :
    ArithmeticProgram (FixedRankOutput n p r) := do
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
    positiveThresholdQuery (fun number t => mainPositiveQueryProgram kernels I S C hr t
      (mainQueryArray I S C g number) (mainInertiaArray I S C g number)) (Fin.cast hcap i)
  let result ← thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive query lower' upper'
  .branch result.selected 0 (fun _ => .pure (zeroFixedRankOutput n p r)) (fun ht =>
    mainStrongThresholdProgram kernels I S C (by omega) ⟨result.selected,lt_of_not_ge ht⟩
      (mainStrongArray I S C g))

def mainBracketWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (Ck p0 : ℝ) : ℕ :=
  12+I.queryCap*(8+mainQueryWorkCap kernels I S C hr Ck p0)+
    mainStrongWorkCap kernels I S C (by omega)

theorem mainBracketProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ) :
    (mainBracketProgram kernels I S C hr g lower upper).work ≤
      mainBracketWorkCap kernels I S C hr Ck p0 := by
  let ratio := (initializerRatioProgram m I.singleFailure).certify.eval
  let budget := (mul 16 ratio.val).certify.eval
  have hbudget : budget.val=16*initializerRatio m I.singleFailure := by
    simp only [budget,ratio,certify_eval,eval_mul,initializerRatioProgram_eval]
  have hcap : leastHalvings budget.val I.nearTolerance I.nearTolerance_positive=I.queryCap := by
    rw [hbudget]
    rfl
  let query := fun i : Fin (leastHalvings budget.val I.nearTolerance I.nearTolerance_positive) =>
    positiveThresholdQuery (fun number t => mainPositiveQueryProgram kernels I S C hr t
      (mainQueryArray I S C g number) (mainInertiaArray I S C g number)) (Fin.cast hcap i)
  have hq : ∀ i t, (query i t).work ≤ 1+mainQueryWorkCap kernels I S C hr Ck p0 := by
    intro i t
    exact positiveThresholdQuery_work_le _ _
      (fun number threshold => mainPositiveQueryProgram_work_bound kernels Ck p0 hC hp hK
        I S C hr threshold (mainQueryArray I S C g number) (mainInertiaArray I S C g number)) _ _
  have hs := thresholdSearchCapped_work_le_all budget.val I.nearTolerance I.nearTolerance_positive
    query (1+mainQueryWorkCap kernels I S C hr Ck p0) hq (lower/4) (4*upper)
  rw [hcap] at hs
  have hsum : 7+(1+mainQueryWorkCap kernels I S C hr Ck p0)=
      8+mainQueryWorkCap kernels I S C hr Ck p0 := by omega
  rw [hsum] at hs
  let result := (thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive
    query (lower/4) (4*upper)).eval
  have hf : (ArithmeticProgram.branch result.selected 0
      (fun _ => .pure (zeroFixedRankOutput n p r))
      (fun ht => mainStrongThresholdProgram kernels I S C (by omega)
        ⟨result.selected,lt_of_not_ge ht⟩ (mainStrongArray I S C g))).work ≤
      1+mainStrongWorkCap kernels I S C (by omega) := by
    simp only [ArithmeticProgram.work]
    split_ifs with ht
    · omega
    · exact Nat.add_le_add_left (mainStrongThresholdProgram_work_bound kernels I S C (by omega)
        ⟨result.selected,lt_of_not_ge ht⟩ (mainStrongArray I S C g)) 1
  simp only [mainBracketProgram,work_bind,work_div,work_mul,certify_work,initializerRatioProgram_work,
    eval_div,eval_mul]
  dsimp only [ratio,budget,query,result] at hs hf
  dsimp [mainBracketWorkCap]
  omega

def mainCoreWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) : ℕ :=
  if hr : C.pair.dimension ≤ r then mainExactOutputWorkCap kernels I S C else
    5*kernelEnvelope kernels C.pair.dimension+psdGramCost kernels r+
      3*C.pair.dimension*C.pair.dimension+C.pair.dimension+10+
      mainExactOutputWorkCap kernels I S C+
      mainBracketWorkCap kernels I S C (Nat.lt_of_not_ge hr) Ck p0

theorem mainCoreProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) :
    (mainCoreProgram kernels I S C g).work ≤ mainCoreWorkCap kernels I S C Ck p0 := by
  by_cases hr : C.pair.dimension ≤ r
  · simpa only [mainCoreProgram,mainCoreWorkCap,dif_pos hr] using
      mainSupportExactOutputProgram_work_bound kernels I S C hr
  · have hk : 1 ≤ C.pair.dimension := by omega
    have hi := gaussianInitializerProgram_work_le kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure hk (by omega : r ≤ C.pair.dimension)
    let initializer := (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval
    simp only [mainCoreProgram,mainCoreWorkCap,dif_neg hr,work_bind]
    change _+(match initializer.result with
      | .exact => exactPhysicalOutputProgram kernels I.A I.B
          (mainSupportAction kernels I S C initializer.range.dimension) initializer.range.basis
            initializer.range.dimension_le_cols
      | .bracket lower upper => mainBracketProgram kernels I S C (Nat.lt_of_not_ge hr) g lower upper).work ≤ _
    cases he : initializer.result with
    | exact =>
      have hh := mainExactOutputProgram_work_bound kernels I S C initializer.range.basis
        initializer.range.dimension_le_cols
      simp only [he]
      omega
    | bracket lower upper =>
      have hh := mainBracketProgram_work_bound kernels Ck p0 hC hp hK I S C
        (Nat.lt_of_not_ge hr) g lower upper
      simp only [he]
      omega

end
end HierarchicalAbsoluteSpectral
