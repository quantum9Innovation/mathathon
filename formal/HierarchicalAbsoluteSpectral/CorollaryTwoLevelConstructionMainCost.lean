import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionCost
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionProgram
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelProbability

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L N : ℕ}
attribute [local irreducible] twoLevelFactorStrongProgram twoLevelFactorExactProgram
  mainPositiveQueryProgram gaussianInitializerProgram thresholdSearchCapped

def twoLevelFactorStrongWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  let v := mainStrongDegree I S C hk
  baseConstructionCost kernels C.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
    2*C.pair.dimension*C.pair.dimension+7+
    (4*v+14+(9+3*v+(v+1)*(mainCarriedActionCost kernels I S C r+6*C.pair.dimension*r)+
      C.pair.dimension*r+(kernels n m r).cost+(kernels m C.pair.dimension r).cost+
      (kernels C.pair.dimension C.pair.dimension r).cost+exactRangeWorkCap kernels n r)+
      twoLevelFactorProjectionWorkCap kernels n m p r)

theorem twoLevelFactorMainStrongProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (twoLevelFactorMainStrongProgram kernels I P S C hk t G).work ≤
      twoLevelFactorStrongWorkCap kernels I S C hk := by
  rw [P.eq_canonical I]
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  let bound := (mainConditionProgram I).certify.eval
  have hb : bound.val=mainConditionBound I := by simp only [bound,certify_eval,mainConditionProgram_eval]
  have hU : 1 ≤ bound.val := by rw [hb]; exact mainConditionBound_ge_one I
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by have hh:=I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith
  have hα1 : I.alpha ≤ 1 := by have hh:=I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hs := twoLevelFactorStrongProgram_work_bound kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
    bound.val I.singleFailure I.alpha hk hU hβ hβ1 I.alpha_positive hα1 (columnsMatrix G)
  have hv : strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1=mainStrongDegree I S C hk := by
    dsimp [mainStrongDegree]
    congr 1
  dsimp only at hs
  rw [hv,mainCarriedAction_cost,mainPhysicalMapAction_cost] at hs
  simp only [twoLevelFactorMainStrongProgram,canonicalMainScalars,mainPreparedCarriedAction_eq,
    mainPreparedPhysicalMapAction_eq,work_bind,coarseBaseProgram_work,certify_work,mainConditionProgram_work]
  dsimp only [base,bound] at hs
  dsimp only [twoLevelFactorStrongWorkCap]
  omega

def twoLevelFactorExactWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) : ℕ :=
  Finset.univ.sup (fun w : Fin (r+1) =>
    (kernels n m w.val).cost+(kernels m C.pair.dimension w.val).cost+
      exactRangeWorkCap kernels n w.val+twoLevelFactorProjectionWorkCap kernels n m p r)

theorem twoLevelFactorExactProgram_main_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    {w : ℕ} (U : Matrix (Fin C.pair.dimension) (Fin w) ℝ) (hw : w ≤ r) :
    (twoLevelFactorExactProgram kernels I.A I.B (mainSupportAction kernels I S C w) U hw).work ≤
      twoLevelFactorExactWorkCap kernels I S C := by
  have hh := twoLevelFactorExactProgram_work_bound kernels I.A I.B (mainSupportAction kernels I S C w) U hw
  rw [mainSupportAction_cost] at hh
  exact hh.trans (Finset.le_sup
    (f := fun w : Fin (r+1) => (kernels n m w.val).cost+(kernels m C.pair.dimension w.val).cost+
      exactRangeWorkCap kernels n w.val+twoLevelFactorProjectionWorkCap kernels n m p r)
    (Finset.mem_univ (⟨w,by omega⟩ : Fin (r+1))))

def twoLevelFactorBracketProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ) :
    ArithmeticProgram (TwoLevelFactors n p r) := do
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
  .branch result.selected 0 (fun _ => .pure (zeroTwoLevelFactors n p r)) (fun ht =>
    twoLevelFactorMainStrongProgram kernels I (canonicalMainScalars I) S C (by omega)
      ⟨result.selected,lt_of_not_ge ht⟩ (mainStrongArray I S C g))

theorem twoLevelFactorBracketProgram_work_bound_of_query
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper : ℝ) (Q : ℕ)
    (hQ : ∀ (number : Fin I.queryCap) t,
      (mainPositiveQueryProgram kernels I S C hr t
        (mainQueryArray I S C g number) (mainInertiaArray I S C g number)).work ≤ Q) :
    (twoLevelFactorBracketProgram kernels I S C hr g lower upper).work ≤
      12+I.queryCap*(8+Q)+twoLevelFactorStrongWorkCap kernels I S C (by omega) := by
  let ratio := (initializerRatioProgram m I.singleFailure).certify.eval
  let budget := (mul 16 ratio.val).certify.eval
  have hbudget : budget.val=16*initializerRatio m I.singleFailure := by
    simp only [budget,ratio,certify_eval,eval_mul,initializerRatioProgram_eval]
  have hcap : leastHalvings budget.val I.nearTolerance I.nearTolerance_positive=I.queryCap := by rw [hbudget]; rfl
  let query := fun i : Fin (leastHalvings budget.val I.nearTolerance I.nearTolerance_positive) =>
    positiveThresholdQuery (fun number t => mainPositiveQueryProgram kernels I S C hr t
      (mainQueryArray I S C g number) (mainInertiaArray I S C g number)) (Fin.cast hcap i)
  have hq : ∀ i t, (query i t).work ≤ 1+Q := by
    intro i t
    exact positiveThresholdQuery_work_le _ Q hQ _ _
  have hs := thresholdSearchCapped_work_le_all budget.val I.nearTolerance I.nearTolerance_positive
    query (1+Q) hq (lower/4) (4*upper)
  rw [hcap] at hs
  have he : 7+(1+Q)=8+Q := by omega
  rw [he] at hs
  let result := (thresholdSearchCapped budget.val I.nearTolerance I.nearTolerance_positive query (lower/4) (4*upper)).eval
  have hf : (ArithmeticProgram.branch result.selected 0
      (fun _ => .pure (zeroTwoLevelFactors n p r))
      (fun ht => twoLevelFactorMainStrongProgram kernels I (canonicalMainScalars I) S C
        (by omega) ⟨result.selected,lt_of_not_ge ht⟩ (mainStrongArray I S C g))).work ≤
      1+twoLevelFactorStrongWorkCap kernels I S C (by omega) := by
    simp only [ArithmeticProgram.work]
    split_ifs
    · omega
    · exact Nat.add_le_add_left
        (twoLevelFactorMainStrongProgram_work_bound kernels I (canonicalMainScalars I) S C (by omega) _ _) 1
  simp only [twoLevelFactorBracketProgram,work_bind,work_div,work_mul,certify_work,
    initializerRatioProgram_work,eval_div,eval_mul]
  dsimp only [ratio,budget,query,result] at hs hf
  omega

def twoLevelFactorCoreWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Q : r < C.pair.dimension → ℕ) : ℕ :=
  if hr : C.pair.dimension ≤ r then twoLevelFactorExactWorkCap kernels I S C else
    5*kernelEnvelope kernels C.pair.dimension+psdGramCost kernels r+
      3*C.pair.dimension*C.pair.dimension+C.pair.dimension+10+
      twoLevelFactorExactWorkCap kernels I S C+
      (12+I.queryCap*(8+Q (Nat.lt_of_not_ge hr))+twoLevelFactorStrongWorkCap kernels I S C (by omega))

theorem twoLevelFactorCoreProgram_work_bound_of_query
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (g : MainRandomTape I)
    (Q : r < C.pair.dimension → ℕ)
    (hQ : ∀ hr (number : Fin I.queryCap) t,
      (mainPositiveQueryProgram kernels I S C hr t
        (mainQueryArray I S C g number) (mainInertiaArray I S C g number)).work ≤ Q hr) :
    (twoLevelFactorCoreProgram kernels I P S C g).work ≤ twoLevelFactorCoreWorkCap kernels I S C Q := by
  rw [P.eq_canonical I]
  by_cases hr : C.pair.dimension ≤ r
  · simpa only [twoLevelFactorCoreProgram,twoLevelFactorCoreWorkCap,dif_pos hr] using
      twoLevelFactorExactProgram_main_work_bound kernels I S C (1 : Core C.pair.dimension) hr
  · have hk : 1 ≤ C.pair.dimension := by omega
    have hi := gaussianInitializerProgram_work_le kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure hk (by omega : r ≤ C.pair.dimension)
    let initializer := (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval
    simp only [twoLevelFactorCoreProgram,twoLevelFactorCoreWorkCap,dif_neg hr,canonicalMainScalars,
      mainPreparedPositiveQueryProgram_eq,work_bind]
    change _+(match initializer.result with
      | .exact => twoLevelFactorExactProgram kernels I.A I.B
          (mainSupportAction kernels I S C initializer.range.dimension) initializer.range.basis initializer.range.dimension_le_cols
      | .bracket lower upper => twoLevelFactorBracketProgram kernels I S C (Nat.lt_of_not_ge hr) g lower upper).work ≤ _
    cases he : initializer.result with
    | exact =>
      have hh := twoLevelFactorExactProgram_main_work_bound kernels I S C initializer.range.basis initializer.range.dimension_le_cols
      simp only [he]
      omega
    | bracket lower upper =>
      have hh := twoLevelFactorBracketProgram_work_bound_of_query kernels I S C (Nat.lt_of_not_ge hr)
        g lower upper (Q (Nat.lt_of_not_ge hr)) (hQ (Nat.lt_of_not_ge hr))
      simp only [he]
      omega

def twoLevelFactorFixedWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (R : ℕ → ℕ → ℕ) (I : FixedProblem n m p r L) (g : MainRandomTape I) (Ck p0 : ℝ) : ℕ :=
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  4*L+3*I.queryCap+2*I.repetitions+29+
    (L+1)*(sketchFormationCap n m I.sketchFailure+sketchFormationCap p m I.sketchFailure)+
    coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
    twoLevelFactorCoreWorkCap kernels I S C (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck p0)

theorem twoLevelFactorFixedProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a → (orthogonalRangeProgram kernels Y).work ≤ R a b)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^p0)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (twoLevelFactorFixedProgram kernels I g).work ≤ twoLevelFactorFixedWorkCap kernels R I g Ck p0 := by
  let P := (mainScalarProgram I).eval
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have hs := mainSketchProgram_work_le I g
  have hc := coarseSupportProgram_work_bound kernels S.initialA S.initialB (I.rank_positive.trans I.rank_le_core)
  have hm := twoLevelFactorCoreProgram_work_bound_of_query kernels I P S C g
    (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck p0) (by
      intro hr number t
      exact mainPositiveQueryProgram_work_bound_flexible kernels R hR Ck p0 hC hp hK I S C hr t _ _)
  simp only [twoLevelFactorFixedProgram,work_bind,mainScalarProgram_work,mainPreparedSketchProgram_eq]
  dsimp only [S,C,P] at hc hm
  dsimp only [twoLevelFactorFixedWorkCap]
  omega

theorem twoLevelConstructionExplicitWork_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^p0)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    twoLevelConstructionExplicitWork kernels I g ≤ m*(N+N)+2*N*r+
      Fintype.card (MainGaussianIndex N m N r 1 I.fixed.queryCap I.fixed.repetitions)+
      (twoLevelParametersProgram m).work+
      twoLevelFactorFixedWorkCap kernels (rangeDeflationWorkCap kernels) I.fixed g Ck p0 := by
  have hbody := twoLevelFactorFixedProgram_work_bound kernels (rangeDeflationWorkCap kernels)
    (rangeDeflationWorkCap_correct kernels hClassical) Ck p0 hC hp hK I.fixed g
  have hw := (twoLevelConstructionProgram kernels I g).eval.width_le
  have hentries : N*(twoLevelConstructionProgram kernels I g).eval.width+
      (twoLevelConstructionProgram kernels I g).eval.width*N ≤ 2*N*r := by nlinarith
  have hwork : (twoLevelConstructionProgram kernels I g).work =
      (twoLevelParametersProgram m).work+(twoLevelFactorFixedProgram kernels I.fixed g).work := by
    simp only [twoLevelConstructionProgram,work_bind,TwoLevelProblem.factorScalarCaller_eq]
  unfold twoLevelConstructionExplicitWork mainRandomizedWork
  rw [hwork]
  omega

end
end HierarchicalAbsoluteSpectral
