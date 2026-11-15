import HierarchicalAbsoluteSpectral.BaseFixedPaperTotal

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
variable {n m p r L : ℕ}

/-- Only dimension, supplied-accuracy, failure and finite scalar-loop
budgets occur in this common logarithmic overhead. -/
def fixedPaperLogBudget (I : FixedProblem n m p r L) : ℝ :=
  1+(fixedSketchLogFactor I:ℝ)+I.queryCap+I.repetitions+fixedOuterLogBudget I+
    fixedFineLog I+fixedRefinementLog I+fixedTrueNeumannLog I+baseFixedInitialLog I

theorem fixedPaperLogBudget_bounds (I : FixedProblem n m p r L) :
    let U := fixedPaperLogBudget I
    1 ≤ U ∧ (fixedSketchLogFactor I:ℝ) ≤ U ∧ (I.queryCap:ℝ) ≤ U ∧
      (I.repetitions:ℝ) ≤ U ∧ fixedOuterLogBudget I ≤ U ∧ fixedFineLog I ≤ U ∧
      fixedRefinementLog I ≤ U ∧ fixedTrueNeumannLog I ≤ U ∧ baseFixedInitialLog I ≤ U := by
  intro U
  have hs : (0:ℝ)≤fixedSketchLogFactor I := Nat.cast_nonneg _
  have hc : (0:ℝ)≤I.queryCap := Nat.cast_nonneg _
  have hr : (0:ℝ)≤I.repetitions := Nat.cast_nonneg _
  have hO:=fixedOuterLogBudget_ge_one I
  have hF:=fixedFineLog_ge_one I
  have hR:=fixedRefinementLog_ge_one I
  have hT:=fixedTrueNeumannLog_ge_one I
  have hB:=baseFixedInitialLog_ge_one I
  dsimp [U,fixedPaperLogBudget]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

def fixedPaperDepthScale (L : ℕ) : ℝ :=
  200*Real.sqrt (1000000*(hierarchyConstant L+1))+1

theorem fixedPaperDepthScale_ge_one (L : ℕ) : 1 ≤ fixedPaperDepthScale L := by
  have hh:=Real.sqrt_nonneg (1000000*(hierarchyConstant L+1))
  unfold fixedPaperDepthScale
  linarith

theorem fixedOuterAccuracyConstant_log_bound (I : FixedProblem n m p r L) :
    fixedOuterAccuracyConstant I ≤ fixedPaperDepthScale L*fixedPaperLogBudget I := by
  have hb:=fixedPaperLogBudget_bounds I
  have hroot:=Real.sqrt_nonneg (1000000*(hierarchyConstant L+1))
  have hm:=mul_le_mul_of_nonneg_right hb.2.2.2.2.1 hroot
  unfold fixedOuterAccuracyConstant fixedPaperDepthScale
  nlinarith only [hb.1,hm]

theorem fixedPaperWorkCoefficient_log_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperWorkCoefficient Ck I ≤
      500*(Ck+1)*fixedPaperDepthScale L*(200000000000:ℝ)^L*(fixedPaperLogBudget I)^(2*L+2) := by
  let U := fixedPaperLogBudget I
  let D := fixedPaperDepthScale L
  let Q := U^(2*L+2)
  let Z := D*(200000000000:ℝ)^L*Q
  have hb:=fixedPaperLogBudget_bounds I
  have hU : 1 ≤ U := hb.1
  have hU0 : 0 ≤ U := by linarith
  have hD : 1 ≤ D := fixedPaperDepthScale_ge_one L
  have hD0 : 0 ≤ D := by linarith
  have hCpow : 1 ≤ (200000000000:ℝ)^L := one_le_pow₀ (by norm_num)
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hU2Q : U^2 ≤ Q := pow_le_pow_right₀ hU (by omega)
  have hU2 : U ≤ U^2 := by nlinarith
  have hU2one : 1 ≤ U^2 := by nlinarith
  have hCQU2 : U^2 ≤ (200000000000:ℝ)^L*Q := by
    have hh:=mul_le_mul hCpow hU2Q (sq_nonneg U) (show 0≤(200000000000:ℝ)^L by positivity)
    simpa only [one_mul] using hh
  have hZDU2 : D*U^2 ≤ Z := by
    simpa only [Z,mul_assoc] using mul_le_mul_of_nonneg_left hCQU2 hD0
  have hDU2 : U^2 ≤ D*U^2 := by nlinarith [mul_le_mul_of_nonneg_right hD (sq_nonneg U)]
  have hUZ : U ≤ Z := hU2.trans (hDU2.trans hZDU2)
  have hZ1 : 1 ≤ Z := hU.trans hUZ
  have hZ0 : 0 ≤ Z := by linarith
  have hScale : fixedOuterAccuracyConstant I ≤ D*U := fixedOuterAccuracyConstant_log_bound I
  have hFine : fixedFineLog I ≤ U := hb.2.2.2.2.2.1
  have hRef : fixedRefinementLog I ≤ U := hb.2.2.2.2.2.2.1
  have hTrue : fixedTrueNeumannLog I ≤ U := hb.2.2.2.2.2.2.2.1
  have hBase : baseFixedInitialLog I ≤ U := hb.2.2.2.2.2.2.2.2
  have hFine0 : 0 ≤ fixedFineLog I := le_trans (by norm_num) (fixedFineLog_ge_one I)
  have hRef0 : 0 ≤ fixedRefinementLog I := le_trans (by norm_num) (fixedRefinementLog_ge_one I)
  have hScale0 : 0 ≤ fixedOuterAccuracyConstant I := le_trans (by norm_num) (fixedOuterAccuracyConstant_ge_one I)
  have hRef2 : (fixedRefinementLog I)^2 ≤ U^2 := pow_le_pow_left₀ hRef0 hRef 2
  have hMult : (fixedRefinementCostMultiplier I)^L ≤ (200000000000*U^2)^L := by
    apply pow_le_pow_left₀ (le_trans (by norm_num) (fixedRefinementCostMultiplier_ge_one I))
    exact mul_le_mul_of_nonneg_left hRef2 (by norm_num)
  have hMult0 : 0 ≤ (fixedRefinementCostMultiplier I)^L :=
    pow_nonneg (le_trans (by norm_num) (fixedRefinementCostMultiplier_ge_one I)) _
  have hFineC : fixedPaperFineCoefficient I ≤ 84*Z := by
    calc
      _ = 84*fixedOuterAccuracyConstant I*fixedFineLog I*(fixedRefinementCostMultiplier I)^L := rfl
      _ ≤ 84*(D*U)*U*(200000000000*U^2)^L := by gcongr
      _ = 84*Z := by
        dsimp [Z,Q]
        rw [mul_pow,←pow_mul,pow_add]
        norm_num
        ring
  have hTrueC : 40*fixedTrueNeumannLog I+2 ≤ 42*U := by linarith
  have hInput : fixedPaperInputCoefficient I ≤ 42*Z := by
    have hh:=mul_le_mul hTrueC hScale hScale0 (show 0≤42*U by positivity)
    have hh' : fixedPaperInputCoefficient I ≤ 42*(D*U^2) := by
      unfold fixedPaperInputCoefficient
      nlinarith only [hh]
    exact hh'.trans (mul_le_mul_of_nonneg_left hZDU2 (by norm_num))
  have hCore : 311*(Ck+1)*baseFixedInitialLog I ≤ 311*(Ck+1)*Z :=
    mul_le_mul_of_nonneg_left (hBase.trans hUZ) (by positivity)
  have hconst : (23:ℝ) ≤ 23*Z := by nlinarith
  calc
    _ ≤ 500*(Ck+1)*Z := by
      unfold fixedPaperWorkCoefficient
      nlinarith [mul_nonneg hC hZ0]
    _ = _ := by dsimp [Z,D,Q,U]; ring

end
end HierarchicalAbsoluteSpectral
