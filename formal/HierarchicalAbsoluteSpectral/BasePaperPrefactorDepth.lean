import HierarchicalAbsoluteSpectral.BasePaperPrefactorTotal
import HierarchicalAbsoluteSpectral.RuntimeFamilyConstants
import HierarchicalAbsoluteSpectral.RuntimeFamilyBounds

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
variable {n m p r L : ℕ}

theorem fixedPaperDepthScale_exponential (L : ℕ) :
    fixedPaperDepthScale L ≤ 1400001*(10:ℝ)^L := by
  have hh:=family_accuracyScale_sqrt_bound L
  rw [accuracyScale_eq_hierarchyConstant] at hh
  have hpow : 1 ≤ (10:ℝ)^L := one_le_pow₀ (by norm_num)
  unfold fixedPaperDepthScale
  nlinarith

theorem fixedPaperDepthConstant_exponential (L : ℕ) :
    fixedPaperDepthConstant L ≤ 40000000000000*(L+1:ℕ)*(2000000000000:ℝ)^L := by
  have hd:=fixedPaperDepthScale_exponential L
  calc
    _ = 23000000*(L+1:ℕ)*fixedPaperDepthScale L*(200000000000:ℝ)^L := rfl
    _ ≤ 23000000*(L+1:ℕ)*(1400001*(10:ℝ)^L)*(200000000000:ℝ)^L := by gcongr
    _ = 32200023000000*(L+1:ℕ)*(2000000000000:ℝ)^L := by
      rw [show (2000000000000:ℝ)=10*200000000000 by norm_num,mul_pow]
      ring
    _ ≤ _ := by gcongr <;> norm_num

/-- The exact prepared-program overhead has the uniform growing-depth
shape: a polynomial outside one power of `constant * logarithm²`.
No multiplication-kernel overhead is raised to the depth here. -/
theorem fixedPaperExplicitPrefactor_product_bound
    (Ck : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperExplicitPrefactor Ck I ≤
      40000000000000*(Ck+1)*(L+1:ℕ)*(fixedPaperLogBudget I)^4*
        (2000000000000*(fixedPaperLogBudget I)^2)^L := by
  have hh:=fixedPaperExplicitPrefactor_log_bound Ck hC I
  have hd:=fixedPaperDepthConstant_exponential L
  have hm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity : 0≤Ck+1))
    (show 0≤(fixedPaperLogBudget I)^(2*L+4) by
      have hu: 1≤fixedPaperLogBudget I := (fixedPaperLogBudget_bounds I).1
      positivity)
  apply hh.trans (hm.trans_eq ?_)
  rw [mul_pow,←pow_mul,pow_add]
  ring

end
end HierarchicalAbsoluteSpectral
