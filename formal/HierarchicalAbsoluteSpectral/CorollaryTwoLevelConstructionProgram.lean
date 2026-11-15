import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionOutput

/-! The same prepared sketch/support/threshold pipeline, with its final
suffix returning only the computed factors. Dense expansion is separate. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L N : ℕ}

def twoLevelFactorMainStrongProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) : ArithmeticProgram (TwoLevelFactors n p r) := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  twoLevelFactorStrongProgram kernels I.A I.B
    (mainPreparedCarriedAction kernels I P S C t.val base r)
    (mainPreparedPhysicalMapAction kernels I P S C t.val base r)
    bound.val P.singleFailure.val P.alpha.val hk
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [P.singleFailure.property]; exact div_pos I.delta_positive (by norm_num))
    (by rw [P.singleFailure.property]; have := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    (by rw [P.alpha.property]; exact I.alpha_positive)
    (by rw [P.alpha.property]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    (columnsMatrix G)

theorem twoLevelFactorMainStrongProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (twoLevelFactorMainStrongProgram kernels I P S C hk t G).eval =
      (mainPreparedStrongThresholdProgram kernels I P S C hk t G).eval.twoLevelFactors := by
  simp only [twoLevelFactorMainStrongProgram,mainPreparedStrongThresholdProgram,eval_bind,
    twoLevelFactorStrongProgram_eval]

theorem twoLevelFactorMainStrongProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (twoLevelFactorMainStrongProgram kernels I P S C hk t G).admissible := by
  simp only [twoLevelFactorMainStrongProgram,admissible_bind,coarseBaseProgram_admissible,
    certify_admissible,mainConditionProgram_admissible,twoLevelFactorStrongProgram_admissible,and_self]

def twoLevelFactorCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) : ArithmeticProgram (TwoLevelFactors n p r) :=
  if hrank : C.pair.dimension ≤ r then
    twoLevelFactorExactProgram kernels I.A I.B (mainSupportAction kernels I S C _) (1 : Core C.pair.dimension) hrank
  else do
    let initializer ← gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) P.singleFailure.val
    match initializer.result with
    | .exact =>
      twoLevelFactorExactProgram kernels I.A I.B
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
      .branch result.selected 0 (fun _ => .pure (zeroTwoLevelFactors n p r)) (fun ht =>
        twoLevelFactorMainStrongProgram kernels I P S C (by omega) ⟨result.selected,lt_of_not_ge ht⟩
          (mainStrongArray I S C g))

theorem twoLevelFactorCoreProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (g : MainRandomTape I) :
    (twoLevelFactorCoreProgram kernels I P S C g).eval =
      (mainPreparedCoreProgram kernels I P S C g).eval.twoLevelFactors := by
  unfold twoLevelFactorCoreProgram mainPreparedCoreProgram
  split_ifs with hrank
  · exact twoLevelFactorExactProgram_eval kernels I.A I.B _ _ hrank
  · simp only [eval_bind]
    split
    · rename_i hcase
      simp only [hcase]
      exact twoLevelFactorExactProgram_eval kernels I.A I.B _ _ _
    · rename_i lower upper hcase
      simp only [hcase,eval_bind]
      simp only [ArithmeticProgram.eval]
      split_ifs
      · rfl
      · exact twoLevelFactorMainStrongProgram_eval kernels I P S C _ _ _

theorem twoLevelFactorCoreProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (g : MainRandomTape I) :
    (twoLevelFactorCoreProgram kernels I P S C g).admissible := by
  rw [P.eq_canonical I]
  unfold twoLevelFactorCoreProgram
  split_ifs with hrank
  · exact twoLevelFactorExactProgram_admissible kernels I.A I.B _ _ hrank
  · have hk : 1 ≤ C.pair.dimension := by omega
    have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
    simp only [canonicalMainScalars,admissible_bind,
      gaussianInitializerProgram_admissible kernels _ _ _ hk hβ,true_and]
    split
    · exact twoLevelFactorExactProgram_admissible kernels I.A I.B _ _ _
    · simp only [admissible_bind,admissible_div,admissible_mul,certify_admissible,
        initializerRatioProgram_admissible m I.singleFailure hβ.ne',true_and,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
      constructor
      · apply thresholdSearchCapped_admissible_all
        intro i t
        apply positiveThresholdQuery_admissible
        intro number threshold
        rw [mainPreparedPositiveQueryProgram_eq]
        exact mainPositiveQueryProgram_admissible kernels I S C _ threshold _ _
      · simp only [ArithmeticProgram.admissible]
        split_ifs
        exact twoLevelFactorMainStrongProgram_admissible kernels I _ S C hk _ _

def twoLevelFactorFixedProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) : ArithmeticProgram (TwoLevelFactors n p r) := do
  let P ← mainScalarProgram I
  let S ← mainPreparedSketchProgram I P g
  let C ← coarseSupportProgram kernels S.initialA S.initialB
  twoLevelFactorCoreProgram kernels I P S C g

theorem twoLevelFactorFixedProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (twoLevelFactorFixedProgram kernels I g).eval =
      (preparedFixedDepthProgram kernels I g).eval.twoLevelFactors := by
  simp only [twoLevelFactorFixedProgram,preparedFixedDepthProgram,mainPreparedPipelineProgram,
    eval_bind,twoLevelFactorCoreProgram_eval]

theorem twoLevelFactorFixedProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (twoLevelFactorFixedProgram kernels I g).admissible := by
  simp only [twoLevelFactorFixedProgram,admissible_bind,mainScalarProgram_admissible,true_and,
    mainPreparedSketchProgram_eq,mainSketchProgram_admissible,coarseSupportProgram_admissible,
    twoLevelFactorCoreProgram_admissible,and_self]

def TwoLevelProblem.factorScalarCaller (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ))
    (g : MainRandomTape I.fixed) : ArithmeticProgram (TwoLevelFactors N N r) :=
  twoLevelFactorFixedProgram kernels (I.fixedFromScalars out) ((I.fixedFromScalars_eq out).symm ▸ g)

theorem TwoLevelProblem.factorScalarCaller_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (out : TwoLevelScalarParameters (m:ℝ)) (g : MainRandomTape I.fixed) :
    I.factorScalarCaller kernels out g = twoLevelFactorFixedProgram kernels I.fixed g := by
  rw [out.eq_canonical]
  rfl

def twoLevelConstructionProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) : ArithmeticProgram (TwoLevelFactors N N r) := do
  let out ← twoLevelParametersProgram m
  I.factorScalarCaller kernels out g

theorem twoLevelConstructionProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelConstructionProgram kernels I g).eval = (fixedDepthProgram kernels I.fixed g).eval.twoLevelFactors := by
  simp only [twoLevelConstructionProgram,eval_bind,TwoLevelProblem.factorScalarCaller_eq,
    twoLevelFactorFixedProgram_eval,preparedFixedDepthProgram_eval]

theorem twoLevelConstructionProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelConstructionProgram kernels I g).admissible := by
  simp only [twoLevelConstructionProgram,admissible_bind,twoLevelParametersProgram_admissible,
    true_and,TwoLevelProblem.factorScalarCaller_eq,twoLevelFactorFixedProgram_admissible]

def twoLevelConstructAndExpandProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) : ArithmeticProgram (FixedRankOutput N N r) := do
  let out ← twoLevelConstructionProgram kernels I g
  twoLevelExpandProgram kernels out

theorem twoLevelConstructAndExpandProgram_product (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelConstructAndExpandProgram kernels I g).eval.product =
      (fixedDepthProgram kernels I.fixed g).eval.product := by
  simp only [twoLevelConstructAndExpandProgram,eval_bind,twoLevelExpandProgram_eval,
    twoLevelConstructionProgram_eval,FixedRankOutput.twoLevelFactors_product]

theorem twoLevelConstructAndExpandProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    (twoLevelConstructAndExpandProgram kernels I g).work =
      (twoLevelConstructionProgram kernels I g).work+
        (kernels N (twoLevelConstructionProgram kernels I g).eval.width N).cost := by
  simp only [twoLevelConstructAndExpandProgram,work_bind,twoLevelExpandProgram_work]

end
end HierarchicalAbsoluteSpectral
