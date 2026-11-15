import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregationRange
import HierarchicalAbsoluteSpectral.BaseFixedActionBudget
import HierarchicalAbsoluteSpectral.BaseFixedCoreAlgebraCostMain

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {n m p r L : ℕ}

def fixedQueryCoreBudget (I : FixedProblem n m p r L) (Ck exponent : ℝ) : ℝ :=
  300*(Ck+1)*(m:ℝ)^exponent*baseFixedInitialLog I+fixedQueryRangeBudget I Ck exponent

theorem fixedQueryCoreBudget_bounds
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    let B := fixedQueryCoreBudget I Ck exponent
    1 ≤ B ∧
      (baseConstructionCost K C.pair.dimension (I.accuracy 0)
        (I.accuracy_positive 0 (by omega)):ℝ) ≤ B ∧
      (kernelEnvelope K C.pair.dimension:ℝ) ≤ B ∧
      (C.pair.dimension:ℝ)*C.pair.dimension ≤ B ∧
      (psdGramCost K r:ℝ) ≤ B ∧ (C.pair.dimension:ℝ) ≤ B ∧
      (⌈212*(Ck+1)*(C.pair.dimension:ℝ)^exponent⌉₊:ℝ) ≤ B := by
  intro B
  let P := (Ck+1)*(m:ℝ)^exponent
  let H := baseFixedInitialLog I
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hpow1 : 1 ≤ (m:ℝ)^exponent :=
    Real.one_le_rpow (by exact_mod_cast hm) (by linarith)
  have hpow0 := Real.rpow_nonneg (Nat.cast_nonneg m) exponent
  have hP1 : 1 ≤ P := by dsimp [P]; nlinarith
  have hH1 : 1 ≤ H := baseFixedInitialLog_ge_one I
  have hPH : P ≤ P*H := le_mul_of_one_le_right (by linarith) hH1
  have hPH0 : 0 ≤ P*H := by positivity
  have hR0 := fixedQueryRangeBudget_nonneg I Ck exponent hC.le
  have hB : 213*P*H ≤ B := by
    dsimp [B,fixedQueryCoreBudget,P,H]
    nlinarith
  have hPB : P ≤ B := by nlinarith
  have hPowP : (m:ℝ)^exponent ≤ P := by dsimp [P]; nlinarith
  have hCP : Ck*(m:ℝ)^exponent ≤ P := by dsimp [P]; nlinarith
  have hbase := mainBaseSetupCost_core_bound K Ck exponent hC hexponent hK I S C 0
  have hbase' : (baseConstructionCost K C.pair.dimension (I.accuracy 0)
      (I.accuracy_positive 0 (by omega)):ℝ) ≤ 36*P*H := by
    push_cast at hbase
    change _ ≤ 36*P*H
    dsimp only [P,H]
    nlinarith [sq_nonneg (C.pair.dimension:ℝ)]
  have henv := (baseFixedKernelEnvelope_bound K Ck exponent hC hK C.pair.dimension m hm
    C.pair.dimension_le_fin).trans hCP
  have hsq := (baseFixedCore_square_bound exponent hexponent C.pair.dimension m hm
    C.pair.dimension_le_fin).trans hPowP
  have hpsd := baseFixedPSDGramCost_bound K Ck exponent hC hexponent hK r m hm I.rank_le_core
  have hdim := (baseFixedCore_linear_bound exponent hexponent C.pair.dimension m hm
    C.pair.dimension_le_fin).trans hPowP
  have hkpow : (C.pair.dimension:ℝ)^exponent ≤ (m:ℝ)^exponent :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast C.pair.dimension_le_fin) (by linarith)
  have htest0 : 0 ≤ 212*(Ck+1)*(C.pair.dimension:ℝ)^exponent := by positivity
  have hceil := (Nat.ceil_lt_add_one htest0).le
  have htestP : 212*(Ck+1)*(C.pair.dimension:ℝ)^exponent ≤ 212*P := by
    dsimp [P]
    exact mul_le_mul_of_nonneg_left hkpow (by positivity)
  have htest : (⌈212*(Ck+1)*(C.pair.dimension:ℝ)^exponent⌉₊:ℝ) ≤ 213*P := by
    linarith
  refine ⟨hP1.trans hPB,?_,henv.trans hPB,hsq.trans hPB,?_,hdim.trans hPB,?_⟩
  · exact hbase'.trans (by nlinarith)
  · change _ ≤ 9*P at hpsd
    exact hpsd.trans (by nlinarith)
  · exact htest.trans (by nlinarith)

theorem fixedQueryCoreBudget_psd_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    (psdGramCost K r:ℝ) ≤ fixedQueryCoreBudget I Ck exponent :=
  (fixedQueryCoreBudget_bounds K Ck exponent hC hexponent hK I S C).2.2.2.2.1

theorem fixedQueryCoreBudget_dimension_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    (C.pair.dimension:ℝ) ≤ fixedQueryCoreBudget I Ck exponent :=
  (fixedQueryCoreBudget_bounds K Ck exponent hC hexponent hK I S C).2.2.2.2.2.1

/-- Concrete construction of every query numerical obligation from the
literal fixed hierarchy, genuine circuit bounds and deterministic stored
sketch row counts. No successful-probability certificate is assumed. -/
theorem fixedFlexibleQueryEnvelope_concrete
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    FixedFlexibleQueryEnvelope K (rangeDeflationWorkCap K) I S C Ck exponent
      (fixedOuterDegreeEnvelope I) (fixedActionWorkBudget K I S (r+1))
      (fixedQueryCoreBudget I Ck exponent) := by
  rcases fixedActionWorkBudget_bounds K I S C (r+1) (r+1) le_rfl hRowsA hRowsB with
    ⟨hEA,hfactor,htrue,hkernel,hblock,_⟩
  rcases fixedQueryCoreBudget_bounds K Ck exponent hC hexponent hK I S C with
    ⟨hB,hbase,henv,hsq,_,_,htest⟩
  have hBR : fixedQueryRangeBudget I Ck exponent ≤ fixedQueryCoreBudget I Ck exponent := by
    unfold fixedQueryCoreBudget
    have hlog := baseFixedInitialLog_ge_one I
    exact le_add_of_nonneg_left (by positivity)
  exact
    { degree_positive := fixedOuterDegreeEnvelope_ge_one I
      action_degree := hEA
      core_positive := hB
      factor := hfactor
      true_action := htrue
      core_kernel := hkernel
      block_entries := hblock
      base := hbase
      core_envelope := henv
      square_entries := hsq
      query_range := fun hr => (mainQueryRangeDeflation_fixed_budget K Ck exponent hC hexponent hK I S C hr).trans hBR
      test := htest
      query_degree := fun hr => mainQueryDegree_fixed_bound I S C hr }

end
end HierarchicalAbsoluteSpectral
