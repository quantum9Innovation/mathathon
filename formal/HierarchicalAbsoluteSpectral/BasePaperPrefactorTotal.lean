import HierarchicalAbsoluteSpectral.BasePaperPrefactor

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
variable {n m p r L : ℕ}

theorem fixedPaperPreparationCoefficient_log_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperPreparationCoefficient Ck I+3 ≤
      100*(L+1:ℕ)*(Ck+1)*(fixedPaperLogBudget I)^2 := by
  let U := fixedPaperLogBudget I
  have hb:=fixedPaperLogBudget_bounds I
  have hU : 1 ≤ U := hb.1
  have hU0 : 0 ≤ U := by linarith
  have hU2 : U ≤ U^2 := by nlinarith
  have hU21 : 1 ≤ U^2 := by nlinarith
  have hc : (I.queryCap:ℝ) ≤ U := hb.2.2.1
  have hr : (I.repetitions:ℝ) ≤ U := hb.2.2.2.1
  have hs : (fixedSketchLogFactor I:ℝ) ≤ U := hb.2.1
  have hcr : (I.queryCap:ℝ)*I.repetitions ≤ U^2 := by
    have hh:=mul_le_mul hc hr (Nat.cast_nonneg I.repetitions) hU0
    nlinarith only [hh]
  have hL : (0:ℝ)≤L := Nat.cast_nonneg _
  have hconst := mul_le_mul_of_nonneg_left hU21
    (show 0≤10*(L:ℝ)+41+11*(Ck+1) by positivity)
  have hpre : fixedPaperPreparationCoefficient Ck I+3 ≤
      (10*(L:ℝ)+51+11*(Ck+1))*U^2 := by
    unfold fixedPaperPreparationCoefficient
    push_cast
    nlinarith only [hs,hc,hr,hcr,hU2,hconst]
  have hcoef : 10*(L:ℝ)+51+11*(Ck+1) ≤ 100*(L+1:ℕ)*(Ck+1) := by
    push_cast
    nlinarith [mul_nonneg hL hC]
  exact hpre.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg U))

def fixedPaperDepthConstant (L : ℕ) : ℝ :=
  23000000*(L+1:ℕ)*fixedPaperDepthScale L*(200000000000:ℝ)^L

/-- A literal polynomial-overhead bound with explicit dependence on depth.
The only remaining asymptotic input is the common scalar logarithmic budget. -/
theorem fixedPaperExplicitPrefactor_log_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperExplicitPrefactor Ck I ≤
      fixedPaperDepthConstant L*(Ck+1)*(fixedPaperLogBudget I)^(2*L+4) := by
  let U := fixedPaperLogBudget I
  let D := fixedPaperDepthScale L
  let Z := D*(200000000000:ℝ)^L*U^(2*L+4)
  have hb:=fixedPaperLogBudget_bounds I
  have hU : 1 ≤ U := hb.1
  have hU0 : 0 ≤ U := by linarith
  have hD : 1 ≤ D := fixedPaperDepthScale_ge_one L
  have hCP : 1 ≤ (200000000000:ℝ)^L := one_le_pow₀ (by norm_num)
  have hDP : 1 ≤ D*(200000000000:ℝ)^L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hCP)]
  have hPow : 0 ≤ U^(2*L+4) := by positivity
  have hZpow : U^(2*L+4) ≤ Z := by
    have hh:=mul_le_mul_of_nonneg_right hDP hPow
    simpa only [one_mul] using hh
  have hU2pow : U^2 ≤ U^(2*L+4) := pow_le_pow_right₀ hU (by omega)
  have hU2Z := hU2pow.trans hZpow
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hL1 : (1:ℝ) ≤ (L+1:ℕ) := by exact_mod_cast Nat.succ_pos L
  have hprep := fixedPaperPreparationCoefficient_log_bound Ck hC I
  have hprepZ : fixedPaperPreparationCoefficient Ck I+3 ≤ 100*(L+1:ℕ)*(Ck+1)*Z :=
    hprep.trans (mul_le_mul_of_nonneg_left hU2Z (by positivity))
  have hcap : (I.queryCap:ℝ)+1 ≤ 2*U := by have hh:=hb.2.2.1; linarith
  have hrep : (I.repetitions:ℝ)+1 ≤ 2*U := by have hh:=hb.2.2.2.1; linarith
  have hloops : ((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1) ≤ 4*U^2 := by
    have hh:=mul_le_mul hcap hrep
      (show 0≤(I.repetitions:ℝ)+1 by positivity) (show 0≤2*U by positivity)
    nlinarith only [hh]
  have hwork:=fixedPaperWorkCoefficient_log_bound Ck hC I
  have hwork0 : 0 ≤ fixedPaperWorkCoefficient Ck I := by
    rcases fixedPaperCoefficient_nonneg I with ⟨hFine,hInput⟩
    have hlog:=baseFixedInitialLog_ge_one I
    unfold fixedPaperWorkCoefficient
    positivity
  have hmul:=mul_le_mul hloops hwork hwork0 (show 0≤4*U^2 by positivity)
  have hmul': 11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*fixedPaperWorkCoefficient Ck I ≤
      22000000*(Ck+1)*Z := by
    have hh:=mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ)≤11000)
    calc
      _ = 11000*(((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*fixedPaperWorkCoefficient Ck I) := by ring
      _ ≤ 11000*(4*U^2*(500*(Ck+1)*D*(200000000000:ℝ)^L*U^(2*L+2))) := hh
      _ = _ := by
        dsimp only [Z]
        rw [show 2*L+4=(2*L+2)+2 by omega,pow_add]
        ring
  have hmulL : 22000000*(Ck+1)*Z ≤ 22000000*(L+1:ℕ)*(Ck+1)*Z := by
    have hh:=mul_le_mul_of_nonneg_right hL1 (show 0≤22000000*(Ck+1)*Z by positivity)
    nlinarith only [hh]
  have htotal : fixedPaperExplicitPrefactor Ck I ≤ 22000100*(L+1:ℕ)*(Ck+1)*Z := by
    unfold fixedPaperExplicitPrefactor fixedPaperPrefactor
    nlinarith only [hprepZ,hmul',hmulL]
  calc
    _ ≤ 22000100*(L+1:ℕ)*(Ck+1)*Z := htotal
    _ ≤ 23000000*(L+1:ℕ)*(Ck+1)*Z := by gcongr <;> norm_num
    _ = _ := by dsimp [fixedPaperDepthConstant,Z,D,U]; ring

end
end HierarchicalAbsoluteSpectral
