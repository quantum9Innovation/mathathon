import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeMagnitude
import HierarchicalAbsoluteSpectral.CorollaryOptimizedExponents

/-! Exact dimension formulas used by the optimized comparators. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
variable {N m r : ℕ}

def comparatorDimensionTheta (m N : ℕ) : ℝ := (m/N:ℝ)^2*Real.sqrt (m/N:ℝ)

def comparatorAlphaRootConstant : ℝ := 1024*Real.sqrt comparatorAlphaDenominator

theorem comparator_dimension_theta_bounds (hm : 1 ≤ m) (hNm : m ≤ N) :
    0 < comparatorDimensionTheta m N ∧ comparatorDimensionTheta m N ≤ 1 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hN0 : (0:ℝ) < N := by exact_mod_cast hm.trans hNm
  have hp : 0 < (m/N:ℝ) := div_pos hm0 hN0
  have hle : (m/N:ℝ) ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hNm)
  have hs : 0 ≤ Real.sqrt (m/N:ℝ) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (m/N:ℝ) ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hle
  have hsq : (m/N:ℝ)^2 ≤ 1 := by nlinarith
  unfold comparatorDimensionTheta
  refine ⟨by positivity,?_⟩
  nlinarith [mul_le_mul hsq hs1 hs (by norm_num : (0:ℝ) ≤ 1)]

theorem comparator_dimension_inverse_sqrt (hm : 1 ≤ m) (hNm : m ≤ N) :
    1/Real.sqrt (comparatorDimensionTheta m N) = (N/m:ℝ)^(5/4:ℝ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hN0 : (0:ℝ) < N := by exact_mod_cast hm.trans hNm
  have htheta := (comparator_dimension_theta_bounds hm hNm).1
  have hs : 0 < Real.sqrt (comparatorDimensionTheta m N) := Real.sqrt_pos.mpr htheta
  have hlog : Real.log (1/Real.sqrt (comparatorDimensionTheta m N)) =
      (5/4:ℝ)*(Real.log (N:ℝ)-Real.log (m:ℝ)) := by
    rw [one_div,Real.log_inv,Real.log_sqrt htheta.le]
    have hh := optimized_theta_log (m:ℝ) (N:ℝ) hm0 hN0
    change Real.log (comparatorDimensionTheta m N)=(5/2:ℝ)*(Real.log (m:ℝ)-Real.log (N:ℝ)) at hh
    rw [hh]
    ring
  calc
    _ = Real.exp (Real.log (1/Real.sqrt (comparatorDimensionTheta m N))) :=
      (Real.exp_log (one_div_pos.mpr hs)).symm
    _ = Real.exp ((5/4:ℝ)*(Real.log (N:ℝ)-Real.log (m:ℝ))) := by rw [hlog]
    _ = _ := by rw [Real.rpow_def_of_pos (div_pos hN0 hm0),Real.log_div hN0.ne' hm0.ne']; congr 1; ring

theorem comparatorAlphaRootConstant_ge_one : 1 ≤ comparatorAlphaRootConstant := by
  have hh := Real.sqrt_le_sqrt comparatorAlphaDenominator_ge_one
  rw [Real.sqrt_one] at hh
  unfold comparatorAlphaRootConstant
  linarith

theorem comparator_inverse_alpha_dimension_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576)) :
    1/Real.sqrt I.alpha ≤ comparatorAlphaRootConstant*(N/m:ℝ)^(5/4:ℝ) := by
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hb := comparator_dimension_theta_bounds hm I.core_le_rows
  have hcap := comparator_inverse_capped_sqrt (comparatorDimensionTheta m N) hb.1 hb.2
  rw [← htheta] at hcap
  have hh := mul_le_mul_of_nonneg_left hcap (Real.sqrt_nonneg comparatorAlphaDenominator)
  rw [comparator_inverse_alpha_sqrt I haccuracy]
  calc
    _ = Real.sqrt comparatorAlphaDenominator*(1/Real.sqrt I.theta) := by ring
    _ ≤ Real.sqrt comparatorAlphaDenominator*(1024/Real.sqrt (comparatorDimensionTheta m N)) := hh
    _ = comparatorAlphaRootConstant*(1/Real.sqrt (comparatorDimensionTheta m N)) := by unfold comparatorAlphaRootConstant; ring
    _ = _ := by rw [comparator_dimension_inverse_sqrt hm I.core_le_rows]

theorem comparator_dimension_internal_accuracy_log
    (I : FixedProblem N m N r 1)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576)) :
    Real.log (1/I.theta) ≤ Real.log (1/comparatorDimensionTheta m N)+Real.log 1048576 := by
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hb := comparator_dimension_theta_bounds hm I.core_le_rows
  have htheta0 := hb.1
  have hprod : comparatorDimensionTheta m N*(1/1048576) ≤ I.theta := by
    rw [htheta]
    apply le_min
    · nlinarith [hb.1]
    · nlinarith [hb.2]
  have hh := Real.log_le_log (one_div_pos.mpr I.theta_positive)
    (one_div_le_one_div_of_le (by positivity : 0 < comparatorDimensionTheta m N*(1/1048576)) hprod)
  have he : Real.log (1/(comparatorDimensionTheta m N*(1/1048576)))=
      Real.log (1/comparatorDimensionTheta m N)+Real.log 1048576 := by
    rw [one_div,Real.log_inv,Real.log_mul hb.1.ne' (by norm_num),
      Real.log_div (by norm_num) (by norm_num),Real.log_one,one_div,Real.log_inv]
    ring
  rwa [he] at hh

end
end HierarchicalAbsoluteSpectral
