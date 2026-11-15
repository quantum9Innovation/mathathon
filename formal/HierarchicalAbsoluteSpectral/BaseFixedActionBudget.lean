import HierarchicalAbsoluteSpectral.BaseFixedOuterFactorCost
import HierarchicalAbsoluteSpectral.BaseFixedStaticCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedFactorOuterEnvelope (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) : ℝ :=
  (42*fixedOuterAccuracyConstant I*fixedFineLog I*(fixedRefinementCostMultiplier I)^L/
    Real.sqrt (I.accuracy L*I.theta))*fixedFineProductSum K I S b

def fixedInputOuterEnvelope (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (b : ℕ) : ℝ :=
  fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p b:ℝ)

def fixedTrueNeumannLog (I : FixedProblem n m p r L) : ℝ := 1+4*Real.log (1/I.massAccuracy)

def fixedActionWorkBudget (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) : ℝ :=
  2*fixedFactorOuterEnvelope K I S b+(40*fixedTrueNeumannLog I+2)*fixedInputOuterEnvelope K I b

theorem fixedFineProductSum_nonneg
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) :
    0 ≤ fixedFineProductSum K I S b := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le (Nat.cast_nonneg _)

theorem fixedFineProductSum_mono_width
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b B : ℕ) (hb : b ≤ B) :
    fixedFineProductSum K I S b ≤ fixedFineProductSum K I S B := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (mainFineProductCost_mono_width K S j b B hb))
    (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le

theorem fixedFactorOuterEnvelope_nonneg
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) :
    0 ≤ fixedFactorOuterEnvelope K I S b := by
  have hscale:=fixedOuterAccuracyConstant_ge_one I
  have hlog:=fixedFineLog_ge_one I
  have hmult:=fixedRefinementCostMultiplier_ge_one I
  have hsum:=fixedFineProductSum_nonneg K I S b
  dsimp [fixedFactorOuterEnvelope]
  positivity

theorem fixedFactorOuterEnvelope_mono_width
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b B : ℕ) (hb : b ≤ B) :
    fixedFactorOuterEnvelope K I S b ≤ fixedFactorOuterEnvelope K I S B := by
  have hscale:=fixedOuterAccuracyConstant_ge_one I
  have hlog:=fixedFineLog_ge_one I
  have hmult:=fixedRefinementCostMultiplier_ge_one I
  exact mul_le_mul_of_nonneg_left (fixedFineProductSum_mono_width K I S b B hb) (by positivity)

theorem fixedTrueNeumannLog_ge_one (I : FixedProblem n m p r L) : 1 ≤ fixedTrueNeumannLog I := by
  have hp := I.final_budget.mass_positive
  have hf := I.final_budget.mass_floor
  change 0 < I.massAccuracy at hp
  change I.massAccuracy ≤ I.accuracy L/100 at hf
  have hb := I.accuracy_bounded L le_rfl
  have hInv : 1 ≤ 1/I.massAccuracy := (le_div_iff₀ hp).mpr (by linarith)
  have hl := Real.log_nonneg hInv
  unfold fixedTrueNeumannLog
  linarith

theorem mainInputProductCost_scalar_floor
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p k b : ℕ) (hk : k ≤ m) : k*b+1 ≤ mainInputProductCost K n m p b := by
  have hh := matrixProductCost_scalar_floor K n m b
  have hm := Nat.mul_le_mul_right b hk
  unfold mainInputProductCost
  omega

theorem fixedInputOuterEnvelope_nonneg
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (b : ℕ) : 0 ≤ fixedInputOuterEnvelope K I b := by
  have hh:=fixedOuterAccuracyConstant_ge_one I
  dsimp [fixedInputOuterEnvelope]
  positivity

theorem fixedInputOuterEnvelope_degree_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (b B : ℕ) (hb : b ≤ B) :
    fixedOuterDegreeEnvelope I*(mainInputProductCost K n m p b:ℝ) ≤ fixedInputOuterEnvelope K I B := by
  have hE:=fixedOuterDegreeEnvelope_ge_one I
  have h1 := mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (mainInputProductCost_mono_width K n m p b B hb)) (show 0≤fixedOuterDegreeEnvelope I by linarith)
  have h2 := mul_le_mul_of_nonneg_right (fixedOuterDegreeEnvelope_le_accuracy_constant I)
    (Nat.cast_nonneg (mainInputProductCost K n m p B))
  exact h1.trans h2

theorem fixedActionWorkBudget_input_le
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) :
    fixedInputOuterEnvelope K I b ≤ fixedActionWorkBudget K I S b := by
  have hf:=fixedFactorOuterEnvelope_nonneg K I S b
  have hi:=fixedInputOuterEnvelope_nonneg K I b
  have ht:=fixedTrueNeumannLog_ge_one I
  unfold fixedActionWorkBudget
  nlinarith

theorem fixedActionWorkBudget_factor_le
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) :
    fixedFactorOuterEnvelope K I S b ≤ fixedActionWorkBudget K I S b := by
  have hf:=fixedFactorOuterEnvelope_nonneg K I S b
  have hi:=fixedInputOuterEnvelope_nonneg K I b
  have ht:=fixedTrueNeumannLog_ge_one I
  unfold fixedActionWorkBudget
  nlinarith

theorem mainFactorActionCost_base_le
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b j : ℕ) :
    (K C.pair.dimension C.pair.dimension b).cost ≤ mainFactorActionCost K I S C b j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    apply ih.trans
    simp only [mainFactorActionCost,refinementActionEnvelope,max_self]
    omega

theorem fixedActionWorkBudget_bounds
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (b B : ℕ) (hb : b ≤ B)
    (hA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    let E := fixedOuterDegreeEnvelope I
    let A := fixedActionWorkBudget K I S B
    E ≤ A ∧
      E*(mainFactorActionCost K I S C b L:ℝ) ≤ A ∧
      E*(mainTrueActionCost K I S C b:ℝ) ≤ A ∧
      E*(K C.pair.dimension C.pair.dimension b).cost ≤ A ∧
      E*(C.pair.dimension:ℝ)*b ≤ A ∧
      E*(mainInputProductCost K n m p b:ℝ) ≤ A := by
  intro E A
  have hE : 1 ≤ E := fixedOuterDegreeEnvelope_ge_one I
  have hE0 : 0 ≤ E := by linarith
  have hinput := fixedInputOuterEnvelope_degree_bound K I b B hb
  have hinputA := hinput.trans (fixedActionWorkBudget_input_le K I S B)
  have hfine := mainFactorActionCost_outer_degree_bound K I S C b hA hB
  have hfactor : E*(mainFactorActionCost K I S C b L:ℝ) ≤ A :=
    hfine.trans ((fixedFactorOuterEnvelope_mono_width K I S b B hb).trans
      (fixedActionWorkBudget_factor_le K I S B))
  have hcore := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (mainFactorActionCost_base_le K I S C b L)) hE0
  have hscalar : (C.pair.dimension:ℝ)*b+1 ≤ (mainInputProductCost K n m p b:ℝ) := by
    exact_mod_cast mainInputProductCost_scalar_floor K n m p C.pair.dimension b C.pair.dimension_le_fin
  have hscalar' := mul_le_mul_of_nonneg_left hscalar hE0
  have hinput1 : 1 ≤ (mainInputProductCost K n m p b:ℝ) := by
    have hh:=mainInputProductCost_scalar_floor K n m p 0 b (Nat.zero_le m)
    have hh' : 1 ≤ mainInputProductCost K n m p b := by simpa only [Nat.zero_mul,Nat.zero_add] using hh
    exact_mod_cast hh'
  have htrue0:=mainTrueActionCost_product_bound K I S C b
  have htrue:=mul_le_mul_of_nonneg_left htrue0 hE0
  have ht:=fixedTrueNeumannLog_ge_one I
  have htrueInput:=mul_le_mul_of_nonneg_left hinput (show 0≤40*fixedTrueNeumannLog I by linarith)
  have hFactor0:=fixedFactorOuterEnvelope_nonneg K I S B
  have hInput0:=fixedInputOuterEnvelope_nonneg K I B
  have htrueA : 40*fixedTrueNeumannLog I*fixedInputOuterEnvelope K I B ≤ A := by
    dsimp [A,fixedActionWorkBudget]
    nlinarith
  have htrue' : E*(mainTrueActionCost K I S C b:ℝ) ≤ A := by
    change E*(mainTrueActionCost K I S C b:ℝ) ≤
      E*(40*fixedTrueNeumannLog I*(mainInputProductCost K n m p b:ℝ)) at htrue
    change _ ≤ 40*fixedTrueNeumannLog I*fixedInputOuterEnvelope K I B at htrueInput
    nlinarith only [htrue,htrueInput,htrueA]
  refine ⟨?_,hfactor,htrue',hcore.trans hfactor,?_,hinputA⟩
  · have hEInput : E ≤ E*(mainInputProductCost K n m p b:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hinput1 hE0]
    exact hEInput.trans hinputA
  · nlinarith only [hscalar',hinputA,hE0]

end
end HierarchicalAbsoluteSpectral
