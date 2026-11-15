import HierarchicalAbsoluteSpectral.BaseFixedOutputCostStrong
import HierarchicalAbsoluteSpectral.BaseFixedActionBudget
import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregationRange

/-! Concrete output callbacks for the fixed-depth paper budgets. No
assumed output-work certificate occurs in these statements. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {n m p r L : ℕ}

theorem mainExactOutputWorkCap_paper_callback
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    let A := fixedActionWorkBudget K I S (r+1)
    let B := 300*fixedOutputCoreCost Ck exponent m*fixedOutputBaseLog I+
      fixedQueryRangeBudget I Ck exponent
    let O := 10*(A+B)+(matrixProductCost K n r p:ℝ)
    (mainExactOutputWorkCap K I S C:ℝ) ≤ O := by
  intro A B O
  let E := fixedOuterDegreeEnvelope I
  let X : ℝ := fixedOutputInputCost K n m p r
  have hE : 1 ≤ E := fixedOuterDegreeEnvelope_ge_one I
  have hb := fixedActionWorkBudget_bounds K I S C (r+1) (r+1) le_rfl hRowsA hRowsB
  have hEA : E ≤ A := hb.1
  have hXA : E*X ≤ A := hb.2.2.2.2.2
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hXA' : X ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hE hX0
    nlinarith only [hh,hXA]
  have hA0 : 0 ≤ A := by linarith
  have hcore := fixedOutputCoreCost_ge_one Ck exponent hC he m (I.rank_positive.trans I.rank_le_core)
  have hcore0 : 0 ≤ fixedOutputCoreCost Ck exponent m := by linarith
  have hlog := fixedOutputBaseLog_ge_one I
  have hmul := mul_le_mul_of_nonneg_left hlog hcore0
  have hrange := fixedQueryRangeBudget_nonneg I Ck exponent hC.le
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hcoreB : 9*fixedOutputCoreCost Ck exponent m ≤ B := by
    dsimp only [B]
    nlinarith only [hmul,hcore0,hrange]
  have hh := mainExactOutputWorkCap_product_bound K Ck exponent hC he hK I S C
  change (mainExactOutputWorkCap K I S C:ℝ) ≤ 5*X+(matrixProductCost K n r p:ℝ)+
    9*fixedOutputCoreCost Ck exponent m at hh
  dsimp only [O]
  linarith only [hh,hXA',hcoreB,hA0,hB0]

theorem mainStrongWorkCap_paper_callback
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension)
    (hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    let A := fixedActionWorkBudget K I S (r+1)
    let B := 300*fixedOutputCoreCost Ck exponent m*fixedOutputBaseLog I+
      fixedQueryRangeBudget I Ck exponent
    let O := 10*(A+B)+(matrixProductCost K n r p:ℝ)
    (mainStrongWorkCap K I S C hk:ℝ) ≤ 100*(A+B+O) := by
  intro A B O
  let E := fixedOuterDegreeEnvelope I
  let X : ℝ := fixedOutputInputCost K n m p r
  let F : ℝ := mainFactorActionCost K I S C r L
  let T : ℝ := mainTrueActionCost K I S C r
  let v : ℝ := mainStrongDegree I S C hk
  have hE : 1 ≤ E := fixedOuterDegreeEnvelope_ge_one I
  have hb := fixedActionWorkBudget_bounds K I S C r (r+1) (by omega) hRowsA hRowsB
  have hbplus := fixedActionWorkBudget_bounds K I S C (r+1) (r+1) le_rfl hRowsA hRowsB
  have hEA : E ≤ A := hb.1
  have hFA : E*F ≤ A := hb.2.1
  have hTA : E*T ≤ A := hb.2.2.1
  have hXA : E*X ≤ A := hbplus.2.2.2.2.2
  have hA0 : 0 ≤ A := by linarith
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hv : v ≤ E := mainStrongDegree_fixed_bound I S C hk
  have hv' : v+1 ≤ 2*E := by linarith
  have hm := mul_le_mul_of_nonneg_right hv'
    (show 0 ≤ 2*F+T+40*X by positivity)
  have hweighted : (v+1)*(2*F+T+40*X) ≤ 86*A := by
    nlinarith only [hm,hFA,hTA,hXA]
  have hcore := fixedOutputCoreCost_ge_one Ck exponent hC he m (I.rank_positive.trans I.rank_le_core)
  have hcore0 : 0 ≤ fixedOutputCoreCost Ck exponent m := by linarith
  have hlog := fixedOutputBaseLog_ge_one I
  have hlog0 : 0 ≤ fixedOutputBaseLog I := by linarith
  have hrange := fixedQueryRangeBudget_nonneg I Ck exponent hC.le
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hcoreB : 60*fixedOutputBaseLog I*fixedOutputCoreCost Ck exponent m ≤ B := by
    have hh := mul_nonneg hlog0 hcore0
    dsimp only [B]
    nlinarith only [hh,hrange]
  have hs : (mainStrongWorkCap K I S C hk:ℝ) ≤
      (v+1)*(2*F+T+40*X)+60*fixedOutputBaseLog I*fixedOutputCoreCost Ck exponent m+
        (matrixProductCost K n r p:ℝ) :=
    mainStrongWorkCap_numeric K Ck exponent hC he hK I S C hk F T le_rfl le_rfl
  have hsmall : (mainStrongWorkCap K I S C hk:ℝ) ≤ 86*A+B+(matrixProductCost K n r p:ℝ) := by
    linarith only [hs,hweighted,hcoreB]
  have hO : (matrixProductCost K n r p:ℝ) ≤ O := by
    dsimp only [O]
    linarith
  have hO0 : 0 ≤ O := (Nat.cast_nonneg _).trans hO
  linarith only [hsmall,hO,hA0,hB0,hO0]

end
end HierarchicalAbsoluteSpectral
