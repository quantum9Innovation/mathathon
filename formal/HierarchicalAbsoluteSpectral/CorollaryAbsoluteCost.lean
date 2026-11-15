import HierarchicalAbsoluteSpectral.CorollaryAbsoluteAlgorithm
import HierarchicalAbsoluteSpectral.BaseMainQueryCost
import HierarchicalAbsoluteSpectral.BaseMainProgramCostOutput

/-! All-outcome costs of the actual arbitrary-rank absolute-threshold caller.
The attempted rank is independent of the positive seed rank. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r s L : ℕ}
attribute [local irreducible] strongProjectionOutputProgram

def absoluteQueryDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : s < C.pair.dimension) : ℕ :=
  krylovDegree C.pair.dimension (mainConditionBound I) (1/2) (I.alpha/100)
    (by omega) (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
    (div_pos I.alpha_positive (by norm_num))
    (by have hh := I.final_budget.alpha_small; change I.alpha ≤ _ at hh; linarith)

def absoluteQueryRangeCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : s < C.pair.dimension) : ℕ :=
  algebraRangeWorkCap kernels C.pair.dimension ((absoluteQueryDegree I S C hr+1)*(s+1))

def absoluteQueryTrialCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : s < C.pair.dimension) (Ck p0 : ℝ) : ℕ :=
  mainFactorActionCost kernels I S C (s+1) L+(kernels C.pair.dimension C.pair.dimension (s+1)).cost+
    (3*absoluteQueryDegree I S C hr+2)*mainThresholdActionCost kernels I S C (s+1)+
    absoluteQueryRangeCap kernels I S C hr+3*kernelEnvelope kernels C.pair.dimension+
      ⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊

def absoluteQueryWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : s < C.pair.dimension) (Ck p0 : ℝ) : ℕ :=
  baseConstructionCost kernels C.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
    2*C.pair.dimension*C.pair.dimension+8+4*absoluteQueryDegree I S C hr+15+
      I.repetitions*absoluteQueryTrialCap kernels I S C hr Ck p0

theorem absolutePositiveQueryProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (absolutePositiveQueryProgram kernels I S C s hr t G g).work ≤ absoluteQueryWorkCap kernels I S C hr Ck p0 := by
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
  have hq : q=absoluteQueryDegree I S C hr := by
    dsimp [q,absoluteQueryDegree]
    congr 1
  let P := mainThresholdAction kernels I S C t.val base (s+1)
  let source := mainSourceAction kernels I S C t.val base (s+1)
  have hRange : ∀ Y : Matrix (Fin C.pair.dimension) (Fin ((q+1)*(s+1))) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ absoluteQueryRangeCap kernels I S C hr := by
    intro Y
    have hh := algebraRangeWorkCap_correct kernels Y (by omega : 1 ≤ max C.pair.dimension ((q+1)*(s+1)))
    have he : algebraRangeWorkCap kernels C.pair.dimension ((q+1)*(s+1)) =
        absoluteQueryRangeCap kernels I S C hr := by rw [hq]; rfl
    exact_mod_cast hh.trans_eq he
  have hauto := columnBlocks_automaticKrylovQueryProgram_work_bound kernels Ck p0 hC hp hK
    (mainThresholdOperator I S C t.val base) (mainThresholdOperator_isHermitian I S C t.val base)
    P (by omega) (mainSourceFactor I S C t.val base) source ⟨s,hr⟩ bound.val ε.val
    (by omega) hbpos hεpos hε1 I.repetitions G g (absoluteQueryRangeCap kernels I S C hr:ℝ) hRange
  have hceil := Nat.le_ceil (212*(Ck+1)*(C.pair.dimension:ℝ)^p0)
  have hP : P.cost=mainThresholdActionCost kernels I S C (s+1) := mainThresholdAction_cost _ _ _ _ _ _ _
  have hS : source.cost=mainFactorActionCost kernels I S C (s+1) L+
      (kernels C.pair.dimension C.pair.dimension (s+1)).cost := mainSourceAction_cost _ _ _ _ _ _ _
  have hautoNat : (automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
      (mainThresholdOperator_isHermitian I S C t.val base) (fun w => P.columnBlocks (by omega) w)
      (mainSourceFactor I S C t.val base) source ⟨s,hr⟩ bound.val ε.val
      (by omega) hbpos hεpos hε1 I.repetitions G g).work ≤
      4*absoluteQueryDegree I S C hr+15+I.repetitions*absoluteQueryTrialCap kernels I S C hr Ck p0 := by
    have htest : (I.repetitions:ℝ)*(212*(Ck+1)*(C.pair.dimension:ℝ)^p0) ≤
        (I.repetitions:ℝ)*⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊ :=
      mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
    change _ ≤ 4*(q:ℝ)+15+(I.repetitions:ℝ)*
      ((source.cost:ℝ)+(3*q+2:ℕ)*P.cost+absoluteQueryRangeCap kernels I S C hr+
        3*kernelEnvelope kernels C.pair.dimension+212*(Ck+1)*(C.pair.dimension:ℝ)^p0) at hauto
    rw [hq,hP,hS] at hauto
    have hh : ((automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
      (mainThresholdOperator_isHermitian I S C t.val base) (fun w => P.columnBlocks (by omega) w)
      (mainSourceFactor I S C t.val base) source ⟨s,hr⟩ bound.val ε.val
      (by omega) hbpos hεpos hε1 I.repetitions G g).work:ℝ) ≤
        (4*absoluteQueryDegree I S C hr+15+I.repetitions*absoluteQueryTrialCap kernels I S C hr Ck p0:ℕ) := by
      dsimp [absoluteQueryTrialCap]
      push_cast at hauto ⊢
      nlinarith
    exact_mod_cast hh
  simp only [absolutePositiveQueryProgram,work_bind,coarseBaseProgram_work,certify_work,
    mainConditionProgram_work,work_div]
  change _ ≤ _
  dsimp only [base,bound,ε,P,source] at hautoNat
  dsimp [absoluteQueryWorkCap]
  omega

def absoluteStrongDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  strongGaussianDegree C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha hk
    (mainConditionBound_ge_one I)
    (div_pos I.delta_positive (by norm_num))
    (by dsimp [FixedProblem.singleFailure]; linarith [I.delta_lt_one])
    I.alpha_positive (by have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)

def absoluteStrongOutputCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (s : ℕ) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  let v := absoluteStrongDegree I S C hk
  4*v+14+(9+3*v+(v+1)*(mainCarriedActionCost kernels I S C s+6*C.pair.dimension*s)+
    C.pair.dimension*s+(kernels n m s).cost+(kernels m C.pair.dimension s).cost+
    (kernels C.pair.dimension C.pair.dimension s).cost+exactRangeWorkCap kernels n s)+
    projectionOutputWorkCap kernels n m p s

def absoluteStrongWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (s : ℕ) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  baseConstructionCost kernels C.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
    2*C.pair.dimension*C.pair.dimension+7+absoluteStrongOutputCap kernels I S C s hk

theorem absoluteStrongThresholdProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    (absoluteStrongThresholdProgram kernels I S C s hk t G).work ≤ absoluteStrongWorkCap kernels I S C s hk := by
  let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
  let bound := (mainConditionProgram I).certify.eval
  have hb : bound.val=mainConditionBound I := by
    simp only [bound,certify_eval,mainConditionProgram_eval]
  have hU : 1 ≤ bound.val := by rw [hb]; exact mainConditionBound_ge_one I
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    have hh := I.delta_lt_one
    dsimp [FixedProblem.singleFailure]
    linarith
  have hα1 : I.alpha ≤ 1 := by
    have hh := I.final_budget.alpha_small
    change I.alpha ≤ _ at hh
    linarith
  have hs := strongProjectionOutputProgram_work_bound kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base s) (mainPhysicalMapAction kernels I S C t.val base s)
    bound.val I.singleFailure I.alpha hk hU hβ hβ1 I.alpha_positive hα1 (columnsMatrix G)
  have hv : strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1=absoluteStrongDegree I S C hk := by
    dsimp [absoluteStrongDegree]
    congr 1
  change _ ≤ 4*strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1+14+
    (9+3*strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
      hk hU hβ hβ1 I.alpha_positive hα1+
      (strongGaussianDegree C.pair.dimension bound.val I.singleFailure I.alpha
        hk hU hβ hβ1 I.alpha_positive hα1+1)*
        ((mainCarriedAction kernels I S C t.val base s).cost+6*C.pair.dimension*s)+
      C.pair.dimension*s+(mainPhysicalMapAction kernels I S C t.val base s).cost+
      exactRangeWorkCap kernels n s)+projectionOutputWorkCap kernels n m p s at hs
  rw [hv,mainCarriedAction_cost,mainPhysicalMapAction_cost] at hs
  have hs' : (strongProjectionOutputProgram kernels I.A I.B
      (mainCarriedAction kernels I S C t.val base s) (mainPhysicalMapAction kernels I S C t.val base s)
      bound.val I.singleFailure I.alpha hk hU hβ hβ1 I.alpha_positive hα1 (columnsMatrix G)).work ≤
      absoluteStrongOutputCap kernels I S C s hk := by
    dsimp [absoluteStrongOutputCap]
    omega
  simp only [absoluteStrongThresholdProgram,work_bind,coarseBaseProgram_work,certify_work,
    mainConditionProgram_work]
  dsimp only [base,bound] at hs'
  dsimp [absoluteStrongWorkCap]
  omega

def absoluteExactWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (s : ℕ) : ℕ :=
  (kernels n m C.pair.dimension).cost+(kernels m C.pair.dimension C.pair.dimension).cost+
    exactRangeWorkCap kernels n C.pair.dimension+projectionOutputWorkCap kernels n m p s

def absoluteAttemptWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (Ck p0 : ℝ) : ℕ :=
  if hs : s < C.pair.dimension then
    absoluteQueryWorkCap kernels I S C hs Ck p0+absoluteStrongWorkCap kernels I S C s (by omega)
  else absoluteExactWorkCap kernels I S C s

theorem absoluteAttemptProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    (absoluteAttemptProgram kernels I S C s t z).work ≤ absoluteAttemptWorkCap kernels I S C s Ck p0 := by
  unfold absoluteAttemptProgram
  split_ifs with hrank
  · have hs := exactPhysicalOutputProgram_work_bound kernels I.A I.B
      (mainSupportAction kernels I S C C.pair.dimension) (1 : Core C.pair.dimension) hrank
    simp only [work_bind,work_pure,Nat.add_zero]
    rw [absoluteAttemptWorkCap,dif_neg (Nat.not_lt.mpr hrank)]
    simpa only [supportExactOutputProgram,mainSupportAction_cost,absoluteExactWorkCap,Nat.add_assoc] using hs
  · have hs : s < C.pair.dimension := Nat.lt_of_not_ge hrank
    have hq := absolutePositiveQueryProgram_work_bound kernels Ck p0 hC hp hK I S C hs t z.1 z.2.1
    have hout := absoluteStrongThresholdProgram_work_bound kernels I S C s (by omega) t z.2.2
    rw [absoluteAttemptWorkCap,dif_pos hs]
    simp only [work_bind]
    split
    · simp only [work_pure,Nat.add_zero]; omega
    all_goals simp only [work_bind,work_pure,Nat.add_zero]; omega

end
end HierarchicalAbsoluteSpectral
