import HierarchicalAbsoluteSpectral.BaseMainOperatorCost
import HierarchicalAbsoluteSpectral.BaseMainProgramCostQuery

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def algebraRangeWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b : ℕ) : ℕ :=
  2*kernelEnvelope kernels (max a b)+psdGramCost kernels b

theorem algebraRangeWorkCap_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) (h : 1 ≤ max a b) :
    (orthogonalRangeProgram kernels Y).work ≤ algebraRangeWorkCap kernels a b :=
  orthogonalRangeProgram_work_le_size kernels Y (max a b) h (le_max_left _ _) (le_max_right _ _) h

def mainQueryDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) : ℕ :=
  krylovDegree C.pair.dimension (mainConditionBound I) (1/2) (I.alpha/100)
    (by omega) (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
    (div_pos I.alpha_positive (by norm_num))
    (by have hh := I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith)

def mainQueryRangeCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) : ℕ :=
  algebraRangeWorkCap kernels C.pair.dimension ((mainQueryDegree I S C hr+1)*(r+1))

def mainQueryTrialCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (Ck p0 : ℝ) : ℕ :=
  mainFactorActionCost kernels I S C (r+1) L+(kernels C.pair.dimension C.pair.dimension (r+1)).cost+
    (3*mainQueryDegree I S C hr+2)*mainThresholdActionCost kernels I S C (r+1)+
    mainQueryRangeCap kernels I S C hr+3*kernelEnvelope kernels C.pair.dimension+
      ⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊

def mainQueryWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (Ck p0 : ℝ) : ℕ :=
  baseConstructionCost kernels C.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
    2*C.pair.dimension*C.pair.dimension+8+4*mainQueryDegree I S C hr+15+
      I.repetitions*mainQueryTrialCap kernels I S C hr Ck p0

theorem mainPositiveQueryProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (mainPositiveQueryProgram kernels I S C hr t G g).work ≤ mainQueryWorkCap kernels I S C hr Ck p0 := by
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  let bound := (mainConditionProgram I).certify.eval
  let ε := (div I.alpha 100).certify.eval
  have hε : ε.val=I.alpha/100 := by simp only [ε,certify_eval,eval_div]
  have hbound : bound.val=mainConditionBound I := by simp only [bound,certify_eval,mainConditionProgram_eval]
  have hεpos : 0 < ε.val := by rw [hε]; exact div_pos I.alpha_positive (by norm_num)
  have hε1 : ε.val ≤ 1 := by rw [hε]; have hh := I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith
  have hbpos : 1 ≤ bound.val := by rw [hbound]; exact mainConditionBound_ge_one I
  let q := krylovDegree C.pair.dimension bound.val (1/2) ε.val (by omega) hbpos
    (by norm_num) (by norm_num) hεpos hε1
  have hq : q=mainQueryDegree I S C hr := by
    dsimp [q,mainQueryDegree]
    congr 1
  let P := mainThresholdAction kernels I S C t.val base (r+1)
  let source := mainSourceAction kernels I S C t.val base (r+1)
  have hRange : ∀ Y : Matrix (Fin C.pair.dimension) (Fin ((q+1)*(r+1))) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ mainQueryRangeCap kernels I S C hr := by
    intro Y
    have hh := algebraRangeWorkCap_correct kernels Y (by omega : 1 ≤ max C.pair.dimension ((q+1)*(r+1)))
    have he : algebraRangeWorkCap kernels C.pair.dimension ((q+1)*(r+1)) =
        mainQueryRangeCap kernels I S C hr := by rw [hq]; rfl
    exact_mod_cast hh.trans_eq he
  have hauto := columnBlocks_automaticKrylovQueryProgram_work_bound kernels Ck p0 hC hp hK
    (mainThresholdOperator I S C t.val base) (mainThresholdOperator_isHermitian I S C t.val base)
    P (by omega) (mainSourceFactor I S C t.val base) source ⟨r,hr⟩ bound.val ε.val
    (by omega) hbpos hεpos hε1 I.repetitions G g (mainQueryRangeCap kernels I S C hr:ℝ) hRange
  have hceil := Nat.le_ceil (212*(Ck+1)*(C.pair.dimension:ℝ)^p0)
  have hP : P.cost=mainThresholdActionCost kernels I S C (r+1) := mainThresholdAction_cost _ _ _ _ _ _ _
  have hS : source.cost=mainFactorActionCost kernels I S C (r+1) L+
      (kernels C.pair.dimension C.pair.dimension (r+1)).cost := mainSourceAction_cost _ _ _ _ _ _ _
  have hautoNat : (automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
      (mainThresholdOperator_isHermitian I S C t.val base) (fun w => P.columnBlocks (by omega) w)
      (mainSourceFactor I S C t.val base) source ⟨r,hr⟩ bound.val ε.val
      (by omega) hbpos hεpos hε1 I.repetitions G g).work ≤
      4*mainQueryDegree I S C hr+15+I.repetitions*mainQueryTrialCap kernels I S C hr Ck p0 := by
    have htest : (I.repetitions:ℝ)*(212*(Ck+1)*(C.pair.dimension:ℝ)^p0) ≤
        (I.repetitions:ℝ)*⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊ :=
      mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
    change _ ≤ 4*(q:ℝ)+15+(I.repetitions:ℝ)*
      ((source.cost:ℝ)+(3*q+2:ℕ)*P.cost+mainQueryRangeCap kernels I S C hr+
        3*kernelEnvelope kernels C.pair.dimension+212*(Ck+1)*(C.pair.dimension:ℝ)^p0) at hauto
    rw [hq,hP,hS] at hauto
    have hh : ((automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
      (mainThresholdOperator_isHermitian I S C t.val base) (fun w => P.columnBlocks (by omega) w)
      (mainSourceFactor I S C t.val base) source ⟨r,hr⟩ bound.val ε.val
      (by omega) hbpos hεpos hε1 I.repetitions G g).work:ℝ) ≤
        (4*mainQueryDegree I S C hr+15+I.repetitions*mainQueryTrialCap kernels I S C hr Ck p0:ℕ) := by
      dsimp [mainQueryTrialCap]
      push_cast at hauto ⊢
      nlinarith
    exact_mod_cast hh
  simp only [mainPositiveQueryProgram,work_bind,coarseBaseProgram_work,certify_work,
    mainConditionProgram_work,work_div]
  change _ ≤ _
  dsimp only [base,bound,ε,P,source] at hautoNat
  dsimp [mainQueryWorkCap]
  omega

end
end HierarchicalAbsoluteSpectral
