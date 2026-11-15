import HierarchicalAbsoluteSpectral.BaseFixedPolylogCounters
import HierarchicalAbsoluteSpectral.BaseFixedPolylogOuter
import HierarchicalAbsoluteSpectral.BasePaperPrefactorTotal

/-! The fixed-depth tilde overhead is an actual polynomial in logarithms
of the manuscript inputs. The kernel growth constant remains explicit. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
variable {n m p r L : ℕ}

def fixedPolylogGaugeCoefficient (L : ℕ) : ℝ :=
  1+fixedPolylogSketchCoefficient L+2000000+5000000+fixedPolylogOuterCoefficient L+
    fixedPolylogFineCoefficient L+fixedPolylogRefinementCoefficient L+
      fixedPolylogTrueCoefficient L+5

theorem fixedPolylogGaugeCoefficient_pos (L : ℕ) : 0 < fixedPolylogGaugeCoefficient L := by
  have hA := fixedPolylogAlphaScale_ge_one L
  have hAp : 0 < fixedPolylogAlphaScale L := by linarith
  have hB := hierarchyUpper_nonneg L
  unfold fixedPolylogGaugeCoefficient fixedPolylogSketchCoefficient fixedPolylogOuterCoefficient
    fixedPolylogFineCoefficient fixedPolylogRefinementCoefficient fixedPolylogTrueCoefficient
  positivity

theorem fixedPaperLogBudget_polylog_bound (I : FixedProblem n m p r L) :
    fixedPaperLogBudget I ≤ fixedPolylogGaugeCoefficient L*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hsketch := fixedPolylog_sketchLogFactor_bound I
  have hcap := fixedPolylog_queryCap_bound I
  have hrep := fixedPolylog_repetitions_bound I
  have houter := fixedPolylog_outerLog_bound I
  have hfine := fixedPolylog_fineLog_bound I
  have href := fixedPolylog_refinementLog_bound I
  have htrue := fixedPolylog_trueLog_bound I
  have hbase := fixedPolylog_baseLog_bound I
  unfold fixedPaperLogBudget fixedPolylogGaugeCoefficient
  nlinarith only [hz,hsketch,hcap,hrep,houter,hfine,href,htrue,hbase]

def fixedPolylogDepthConstant (L : ℕ) : ℝ :=
  fixedPaperDepthConstant L*(fixedPolylogGaugeCoefficient L)^(2*L+4)

theorem fixedPolylogDepthConstant_pos (L : ℕ) : 0 < fixedPolylogDepthConstant L := by
  have hD := fixedPaperDepthScale_ge_one L
  have hDp : 0 < fixedPaperDepthScale L := by linarith
  have hG := fixedPolylogGaugeCoefficient_pos L
  unfold fixedPolylogDepthConstant fixedPaperDepthConstant
  positivity

/-- The full explicit-output prefactor has fixed-depth polylogarithmic
degree 2L+4. The only non-input constant beyond depth is the displayed
linear factor Ck+1 from the verified kernel growth bound. -/
theorem fixedPaperExplicitPrefactor_polylog_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperExplicitPrefactor Ck I ≤
      (Ck+1)*fixedPolylogDepthConstant L*(fixedPolylogGauge I)^(2*L+4) := by
  have hh := fixedPaperExplicitPrefactor_log_bound Ck hC I
  have hU := (fixedPaperLogBudget_bounds I).1
  have hUg := fixedPaperLogBudget_polylog_bound I
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ fixedPaperLogBudget I) hUg (2*L+4)
  have hD := fixedPaperDepthScale_ge_one L
  have hDp : 0 < fixedPaperDepthScale L := by linarith
  have hscale : 0 ≤ fixedPaperDepthConstant L*(Ck+1) := by
    unfold fixedPaperDepthConstant
    positivity
  have hm := mul_le_mul_of_nonneg_left hpow hscale
  calc
    _ ≤ fixedPaperDepthConstant L*(Ck+1)*(fixedPaperLogBudget I)^(2*L+4) := hh
    _ ≤ fixedPaperDepthConstant L*(Ck+1)*
        (fixedPolylogGaugeCoefficient L*fixedPolylogGauge I)^(2*L+4) := hm
    _ = _ := by unfold fixedPolylogDepthConstant; rw [mul_pow]; ring

theorem fixedPaperPrefactor_polylog_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperPrefactor Ck I ≤
      (Ck+1)*fixedPolylogDepthConstant L*(fixedPolylogGauge I)^(2*L+4) := by
  have hh := fixedPaperExplicitPrefactor_polylog_bound Ck hC I
  unfold fixedPaperExplicitPrefactor at hh
  linarith

/-- For each fixed depth, one positive structural constant works for
every original-input problem and every nonnegative kernel coefficient. -/
theorem fixedPaperPrefactor_is_fixed_depth_polylog (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n m p r : ℕ} (I : FixedProblem n m p r L)
      (Ck : ℝ), 0 ≤ Ck → fixedPaperPrefactor Ck I ≤
        (Ck+1)*C*(fixedPolylogGauge I)^(2*L+4) := by
  refine ⟨fixedPolylogDepthConstant L,fixedPolylogDepthConstant_pos L,?_⟩
  intro n m p r I Ck hC
  exact fixedPaperPrefactor_polylog_bound Ck hC I

theorem fixedPaperExplicitPrefactor_is_fixed_depth_polylog (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n m p r : ℕ} (I : FixedProblem n m p r L)
      (Ck : ℝ), 0 ≤ Ck → fixedPaperExplicitPrefactor Ck I ≤
        (Ck+1)*C*(fixedPolylogGauge I)^(2*L+4) := by
  refine ⟨fixedPolylogDepthConstant L,fixedPolylogDepthConstant_pos L,?_⟩
  intro n m p r I Ck hC
  exact fixedPaperExplicitPrefactor_polylog_bound Ck hC I

end
end HierarchicalAbsoluteSpectral
