import HierarchicalAbsoluteSpectral.BaseMainFlexibleQueryCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}
attribute [local irreducible] mainPositiveQueryProgram mainStrongThresholdProgram
  gaussianInitializerProgram thresholdSearchCapped mainSketchProgram mainCoreProgram

theorem mainBracketProgram_work_bound_of_query
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ) (Q : ℕ)
    (hQ : ∀ (number : Fin I.queryCap) t,
      (mainPositiveQueryProgram kernels I S C hr t
        (mainQueryArray I S C g number) (mainInertiaArray I S C g number)).work ≤ Q) :
    (mainBracketProgram kernels I S C hr g lower upper).work ≤
      12+I.queryCap*(8+Q)+mainStrongWorkCap kernels I S C (by omega) := by
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
  have hq : ∀ i t, (query i t).work ≤ 1+Q := by
    intro i t
    exact positiveThresholdQuery_work_le _ Q hQ _ _
  have hs := thresholdSearchCapped_work_le_all budget.val I.nearTolerance I.nearTolerance_positive
    query (1+Q) hq (lower/4) (4*upper)
  rw [hcap] at hs
  have hsum : 7+(1+Q)=8+Q := by omega
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
  omega

def mainCoreWorkCapWithQuery (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Q : r < C.pair.dimension → ℕ) : ℕ :=
  if hr : C.pair.dimension ≤ r then mainExactOutputWorkCap kernels I S C else
    5*kernelEnvelope kernels C.pair.dimension+psdGramCost kernels r+
      3*C.pair.dimension*C.pair.dimension+C.pair.dimension+10+
      mainExactOutputWorkCap kernels I S C+
      (12+I.queryCap*(8+Q (Nat.lt_of_not_ge hr))+mainStrongWorkCap kernels I S C (by omega))

theorem mainCoreProgram_work_bound_of_query
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) (Q : r < C.pair.dimension → ℕ)
    (hQ : ∀ hr (number : Fin I.queryCap) t,
      (mainPositiveQueryProgram kernels I S C hr t
        (mainQueryArray I S C g number) (mainInertiaArray I S C g number)).work ≤ Q hr) :
    (mainCoreProgram kernels I S C g).work ≤ mainCoreWorkCapWithQuery kernels I S C Q := by
  by_cases hr : C.pair.dimension ≤ r
  · simpa only [mainCoreProgram,mainCoreWorkCapWithQuery,dif_pos hr] using
      mainSupportExactOutputProgram_work_bound kernels I S C hr
  · have hk : 1 ≤ C.pair.dimension := by omega
    have hi := gaussianInitializerProgram_work_le kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure hk (by omega : r ≤ C.pair.dimension)
    let initializer := (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval
    simp only [mainCoreProgram,mainCoreWorkCapWithQuery,dif_neg hr,work_bind]
    change _+(match initializer.result with
      | .exact => exactPhysicalOutputProgram kernels I.A I.B
          (mainSupportAction kernels I S C initializer.range.dimension) initializer.range.basis
            initializer.range.dimension_le_cols
      | .bracket lower upper => mainBracketProgram kernels I S C (Nat.lt_of_not_ge hr) g lower upper).work ≤ _
    cases initializer.result with
    | exact =>
      have hh := mainExactOutputProgram_work_bound kernels I S C initializer.range.basis
        initializer.range.dimension_le_cols
      simp only
      omega
    | bracket lower upper =>
      have hh := mainBracketProgram_work_bound_of_query kernels I S C (Nat.lt_of_not_ge hr)
        g lower upper (Q (Nat.lt_of_not_ge hr)) (hQ (Nat.lt_of_not_ge hr))
      simp only
      omega

def fixedDepthFlexibleRealizedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (R : ℕ → ℕ → ℕ) (I : FixedProblem n m p r L) (g : MainRandomTape I) (Ck p0 : ℝ) : ℕ :=
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  (L+1)*(sketchFormationCap n m I.sketchFailure+sketchFormationCap p m I.sketchFailure)+
    coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
    mainCoreWorkCapWithQuery kernels I S C (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck p0)

theorem fixedDepthProgram_work_bound_flexible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a →
      (orthogonalRangeProgram kernels Y).work ≤ R a b)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (fixedDepthProgram kernels I g).work ≤ fixedDepthFlexibleRealizedWorkCap kernels R I g Ck p0 := by
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I g
  have hc := coarseSupportProgram_work_bound kernels S.initialA S.initialB
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)
  have hm := mainCoreProgram_work_bound_of_query kernels I S C g
    (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck p0)
    (fun hr number t => mainPositiveQueryProgram_work_bound_flexible kernels R hR Ck p0 hC hp hK
      I S C hr t (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
  simp only [fixedDepthProgram,work_bind]
  dsimp only [S,C] at hc hm
  dsimp only [fixedDepthFlexibleRealizedWorkCap]
  omega

end
end HierarchicalAbsoluteSpectral
