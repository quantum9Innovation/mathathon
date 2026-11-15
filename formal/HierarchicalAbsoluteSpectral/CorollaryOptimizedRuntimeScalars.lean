import HierarchicalAbsoluteSpectral.RuntimeFamilyLogBudgets
import HierarchicalAbsoluteSpectral.ThresholdKrylovDegree
import HierarchicalAbsoluteSpectral.ThresholdHalving
import HierarchicalAbsoluteSpectral.StrongFilterGaussian

/-! Uniform logarithmic budgets for the actual finite comparator degrees
and scalar halving counters. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

theorem comparator_halving_log_bound (x epsilon H : ℝ) (hx : 0 < x)
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) (hlog : Real.log (x/epsilon) ≤ H) :
    (leastHalvings x epsilon hepsilon:ℝ) ≤ H/Real.log 2+1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℕ := ⌈H/Real.log 2⌉₊
  have hceil := Nat.le_ceil (H/Real.log 2)
  have hpower : x/epsilon ≤ (2:ℝ)^q := by
    apply (Real.log_le_log_iff (div_pos hx hepsilon) (by positivity)).mp
    rw [Real.log_pow]
    have hh := mul_le_mul_of_nonneg_right hceil hlog2.le
    rw [div_mul_cancel₀ _ hlog2.ne'] at hh
    exact hlog.trans hh
  have hstop : x/(2:ℝ)^q ≤ epsilon := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^q)).mpr
    have hh := (div_le_iff₀ hepsilon).mp hpower
    nlinarith
  have hq : leastHalvings x epsilon hepsilon ≤ q := leastHalvings_le x epsilon hepsilon q hstop
  have hqreal : (q:ℝ) ≤ H/Real.log 2+1 := (Nat.ceil_lt_add_one (div_nonneg hH hlog2.le)).le
  exact (by exact_mod_cast hq : (leastHalvings x epsilon hepsilon:ℝ) ≤ q).trans hqreal

theorem comparator_gaussian_log_budget (k : ℕ) (m U beta alpha DU Db Da : ℝ)
    (hk : 1 ≤ k) (hkm : (k:ℝ) ≤ m) (hm : 2 ≤ m)
    (hU : 0 < U) (hb : 0 < beta) (ha : 0 < alpha)
    (hlogU : Real.log U ≤ DU*Real.log m)
    (hlogb : Real.log (1/beta) ≤ Db*Real.log m)
    (hloga : Real.log (1/alpha) ≤ Da*Real.log m) :
    Real.log (20*gaussianCaptureRadius k U beta/alpha) ≤
      (29+3*DU+3*Db+Da)*Real.log m := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hlogk := Real.log_le_log hk0 hkm
  have hm0 : 0 < m := by linarith
  have hlogm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm
  have h100 : Real.log (100:ℝ) ≤ 7*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 100) (by norm_num : (100:ℝ) ≤ 2^7)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have h20 : Real.log (20:ℝ) ≤ 5*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 20) (by norm_num : (20:ℝ) ≤ 2^5)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have he : Real.log (20*gaussianCaptureRadius k U beta/alpha) =
      Real.log 20+3*(Real.log 100+Real.log (k:ℝ)+Real.log U+Real.log (1/beta))+
        Real.log (1/alpha) := by
    unfold gaussianCaptureRadius
    rw [Real.log_div (by positivity) ha.ne',Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_div (by positivity) hb.ne',
      Real.log_mul (by positivity) hU.ne',Real.log_mul (by norm_num) hk0.ne',
      one_div,Real.log_inv,one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith

theorem comparator_krylov_degree_bound (k : ℕ) (m U beta epsilon DU Db De : ℝ)
    (hk : 1 ≤ k) (hkm : (k:ℝ) ≤ m) (hm : 2 ≤ m) (hU : 1 ≤ U)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hlogU : Real.log U ≤ DU*Real.log m)
    (hlogb : Real.log (1/beta) ≤ Db*Real.log m)
    (hloge : Real.log (1/epsilon) ≤ De*Real.log m) :
    (krylovDegree k U beta epsilon hk hU hb hb1 he he1:ℝ) ≤
      20*(29+3*DU+3*Db+De)*Real.log m/Real.sqrt epsilon+1 := by
  have hlog := comparator_gaussian_log_budget k m U beta epsilon DU Db De hk hkm hm
    (by linarith) hb he hlogU hlogb hloge
  have hroot : Real.sqrt (epsilon/100) = Real.sqrt epsilon/10 := by
    rw [Real.sqrt_div he.le]
    norm_num
  have hraw := krylovDegree_bound k U beta epsilon hk hU hb hb1 he he1
  rw [hroot] at hraw
  apply hraw.trans
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 20)) (Real.sqrt_nonneg epsilon)
  convert add_le_add_right hh 1 using 1 <;> ring

theorem comparator_strong_degree_bound (k : ℕ) (m U beta alpha DU Db Da : ℝ)
    (hk : 1 ≤ k) (hkm : (k:ℝ) ≤ m) (hm : 2 ≤ m) (hU : 1 ≤ U)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hlogU : Real.log U ≤ DU*Real.log m)
    (hlogb : Real.log (1/beta) ≤ Db*Real.log m)
    (hloga : Real.log (1/alpha) ≤ Da*Real.log m) :
    (strongGaussianDegree k U beta alpha hk hU hb hb1 ha ha1:ℝ) ≤
      2*(29+3*DU+3*Db+Da)*Real.log m/Real.sqrt alpha+1 := by
  have hlog := comparator_gaussian_log_budget k m U beta alpha DU Db Da hk hkm hm
    (by linarith) hb ha hlogU hlogb hloga
  have hR : 0 < gaussianCaptureRadius k U beta := by unfold gaussianCaptureRadius; positivity
  have hsmall : Real.log (4*gaussianCaptureRadius k U beta/alpha) ≤
      Real.log (20*gaussianCaptureRadius k U beta/alpha) := by
    apply Real.log_le_log (by positivity)
    gcongr
    norm_num
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hsmall.trans hlog) (by norm_num : (0:ℝ) ≤ 2)) (Real.sqrt_nonneg alpha)
  apply (strongGaussianDegree_bound k U beta alpha hk hU hb hb1 ha ha1).trans
  convert (add_le_add_right hh 1) using 1 <;> ring

end
end HierarchicalAbsoluteSpectral
