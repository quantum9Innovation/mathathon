import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregation

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
variable {n m p r L : ℕ}

/-- A uniform range-algebra charge for the actual deflation program. It
retains the fast core branch and the original m*w_K^2 wide-block fallback. -/
def fixedQueryRangeBudget (I : FixedProblem n m p r L) (Ck exponent : ℝ) : ℝ :=
  if fixedKrylovRawWidth I ≤ m then 11*(Ck+1)*(m:ℝ)^exponent
  else 22*(m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2

theorem fixedQueryRangeBudget_nonneg
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (hC : 0 ≤ Ck) :
    0 ≤ fixedQueryRangeBudget I Ck exponent := by
  unfold fixedQueryRangeBudget
  split_ifs <;> positivity

theorem mainQueryRangeDeflation_fixed_budget
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    (rangeDeflationWorkCap kernels C.pair.dimension ((mainQueryDegree I S C hr+1)*(r+1)):ℝ) ≤
      fixedQueryRangeBudget I Ck exponent := by
  unfold fixedQueryRangeBudget
  split_ifs with hwidth
  · exact mainQueryRangeCap_bound_narrow kernels Ck exponent hC hexponent hK I S C hr hwidth
  · have hh := mainQueryRangeCap_bound_wide kernels I S C hr
    have hhR : (rangeDeflationWorkCap kernels C.pair.dimension
        ((mainQueryDegree I S C hr+1)*(r+1)):ℝ) ≤
        ((22*m*fixedKrylovRawWidth I*fixedKrylovRawWidth I:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_mul,pow_two,Nat.cast_ofNat,mul_assoc] using hhR

theorem fixedQueryRangeBudget_bound_arbitrary_width
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (hC : 0 ≤ Ck) :
    fixedQueryRangeBudget I Ck exponent ≤
      11*(Ck+1)*(m:ℝ)^exponent+22*(m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2 := by
  unfold fixedQueryRangeBudget
  have hcore : 0 ≤ 11*(Ck+1)*(m:ℝ)^exponent := by positivity
  have hwide : 0 ≤ 22*(m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2 := by positivity
  split_ifs <;> linarith

theorem fixedQueryRangeBudget_eq_narrow
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (hwidth : fixedKrylovRawWidth I ≤ m) :
    fixedQueryRangeBudget I Ck exponent = 11*(Ck+1)*(m:ℝ)^exponent :=
  if_pos hwidth

end
end HierarchicalAbsoluteSpectral
