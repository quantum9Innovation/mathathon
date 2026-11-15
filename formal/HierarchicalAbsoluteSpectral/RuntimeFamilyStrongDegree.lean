import HierarchicalAbsoluteSpectral.RuntimeFamilyUniformDegrees
import HierarchicalAbsoluteSpectral.StrongFilterGaussian

/-! The final covariance-conditioned degree has only one polynomial factor
from the hierarchy constants. Every logarithm is bounded uniformly in depth. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

def familyCovarianceEnvelope {s : ℝ} (out : FamilyScheduleOutput (1/1024) (s/1024)) : ℝ :=
  (2 : ℝ)^out.depth*Real.sqrt ((1/1024)/out.terminal)

def familyOuterAccuracy {s : ℝ} (out : FamilyScheduleOutput (1/1024) (s/1024)) : ℝ :=
  s^5/(accuracyScale out.depth*out.terminal)

theorem family_accuracyScale_ge_one (L : ℕ) : 1 ≤ accuracyScale L := by
  unfold accuracyScale
  have hh := defectConstant_ge_one L
  nlinarith

theorem family_covariance_accuracy_bounds {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth) :
    1 ≤ familyCovarianceEnvelope out ∧ 0 < familyOuterAccuracy out ∧ familyOuterAccuracy out ≤ 1 := by
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hh : out.terminal ≤ 1/1024 := by rw [out.terminal_eq]; exact out.level_le (by norm_num) (by positivity) _ (le_refl _)
  have hb := out.nonzero_terminal_bounds hs hL
  have hs1 : s ≤ 1 := by linarith
  have hA := family_accuracyScale_ge_one out.depth
  have hAp : 0 < accuracyScale out.depth := by linarith
  have hr : 1 ≤ (1/1024 : ℝ)/out.terminal := (le_div_iff₀ hp).mpr (by linarith)
  have hroot : 1 ≤ Real.sqrt ((1/1024)/out.terminal) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hpow : 1 ≤ (2 : ℝ)^out.depth := one_le_pow₀ (by norm_num)
  refine ⟨?_,by unfold familyOuterAccuracy; positivity,?_⟩
  · unfold familyCovarianceEnvelope
    nlinarith
  · unfold familyOuterAccuracy
    apply (div_le_iff₀ (mul_pos hAp hp)).mpr
    have hs5 : s^5 ≤ s := by
      calc
        _ ≤ s^1 := pow_le_pow_of_le_one hs.le hs1 (by omega)
        _ = s := pow_one _
    nlinarith

theorem family_covariance_log_bound {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth) :
    Real.log (familyCovarianceEnvelope out) ≤
      (out.depth : ℝ)*Real.log 2+(1/2)*Real.log (1/s) := by
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hb := out.nonzero_terminal_bounds hs hL
  have hlo := Real.log_le_log hs hb.1
  have hconst : Real.log (1/1024 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hslog : Real.log (1/s) = -Real.log s := by rw [one_div,Real.log_inv]
  unfold familyCovarianceEnvelope
  rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr (by positivity)).ne',
    Real.log_pow,Real.log_sqrt (by positivity),Real.log_div (by norm_num) hp.ne',
    hslog]
  nlinarith

theorem family_accuracy_log_bound {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m) :
    Real.log (1/familyOuterAccuracy out) ≤ (12*D+26)*Real.log m := by
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hh : out.terminal ≤ 1 := by
    rw [out.terminal_eq]
    have hb := out.level_le (by norm_num) (by positivity) out.depth (le_refl _)
    linarith
  have hlogh : Real.log out.terminal ≤ 0 := Real.log_nonpos hp.le hh
  have hAp : 0 < accuracyScale out.depth := lt_of_lt_of_le (by norm_num) (family_accuracyScale_ge_one _)
  have hA := Real.log_le_log hAp (family_accuracyScale_bound out.depth)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hA
  have hc : Real.log (39000000 : ℝ) ≤ 26*Real.log 2 := by
    have hx := Real.log_le_log (by norm_num : (0 : ℝ) < 39000000)
      (by norm_num : (39000000 : ℝ) ≤ (2 : ℝ)^26)
    rwa [Real.log_pow] at hx
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hx := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hx
  have h100L := mul_le_mul_of_nonneg_left h100 (Nat.cast_nonneg out.depth)
  have hdepth := familySchedule_depth_log_linear hs out hL hscale
  have hslog : Real.log (1/s) = -Real.log s := by rw [one_div,Real.log_inv]
  have he : Real.log (1/familyOuterAccuracy out) =
      Real.log (accuracyScale out.depth)+Real.log out.terminal+5*Real.log (1/s) := by
    unfold familyOuterAccuracy
    rw [one_div,Real.log_inv,Real.log_div (pow_pos hs _).ne' (mul_pos hAp hp).ne',
      Real.log_mul hAp.ne' hp.ne',Real.log_pow,hslog]
    ring
  rw [he]
  nlinarith

theorem family_gaussian_log_budget {s m D Dβ β : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log m) :
    Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out) ≤
      (17*D+3*Dβ+60)*Real.log m := by
  have hbounds := family_covariance_accuracy_bounds hs out hL
  have hU : 0 < familyCovarianceEnvelope out := by linarith [hbounds.1]
  have hα := hbounds.2.1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogk := Real.log_le_log hk0 hkm
  have hlogU := family_covariance_log_bound hs out hL
  have hlogα := family_accuracy_log_bound hs out hL hm hscale
  have hdepth := familySchedule_depth_log_linear hs out hL hscale
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hx := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hx
  have he : Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out) =
      2*Real.log 2+3*(Real.log 100+Real.log (k : ℝ)+Real.log (familyCovarianceEnvelope out)+
        Real.log (1/β))+Real.log (1/familyOuterAccuracy out) := by
    unfold gaussianCaptureRadius
    rw [Real.log_div (by positivity) hα.ne',Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_div (by positivity) hβ.ne',
      Real.log_mul (by positivity) hU.ne',Real.log_mul (by norm_num) hk0.ne',
      one_div,Real.log_inv,one_div,Real.log_inv,
      show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    ring
  rw [he]
  have hlogm0 : 0 ≤ Real.log m := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
  nlinarith [mul_nonneg hD hlogm0]

theorem family_inverse_accuracy_sqrt_bound (s A h : ℝ)
    (hs : 0 < s) (hA : 0 < A) (hh : 0 < h) (hhi : h ≤ 1024*s) :
    1/Real.sqrt (s^5/(A*h)) ≤ 32*Real.sqrt A/s^2 := by
  have hα : 0 < s^5/(A*h) := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (1/Real.sqrt (s^5/(A*h)))^2 = A*h/s^5 := by
      rw [div_pow,one_pow,Real.sq_sqrt hα.le]
      field_simp
    _ ≤ 1024*A/s^4 := by
      apply (div_le_div_iff₀ (pow_pos hs _) (pow_pos hs _)).mpr
      have hh' := mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ A*s^4)
      nlinarith
    _ = (32*Real.sqrt A/s^2)^2 := by
      rw [div_pow,mul_pow,Real.sq_sqrt hA.le]
      norm_num
      ring

theorem family_strong_degree_uniform_bound {s m D Dβ β : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log m) :
    ∃ (hU : 1 ≤ familyCovarianceEnvelope out) (hα : 0 < familyOuterAccuracy out)
      (hα1 : familyOuterAccuracy out ≤ 1),
      (strongGaussianDegree k (familyCovarianceEnvelope out) β (familyOuterAccuracy out)
        hk hU hβ hβ1 hα hα1 : ℝ) ≤
      448000*(17*D+3*Dβ+60)*((10 : ℝ)^out.depth/s^2)*Real.log m+1 := by
  have hb := family_covariance_accuracy_bounds hs out hL
  refine ⟨hb.1,hb.2.1,hb.2.2,?_⟩
  have hu := strongGaussianDegree_bound k (familyCovarianceEnvelope out) β (familyOuterAccuracy out)
    hk hb.1 hβ hβ1 hb.2.1 hb.2.2
  have hlog := family_gaussian_log_budget hs out hL k hk hkm hβ hβ1 hD hm hscale hconfidence
  have hR := gaussianCaptureRadius_ge_one k (familyCovarianceEnvelope out) β hk hb.1 hβ hβ1
  have hB : 0 ≤ Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hb.2.1).mpr
    linarith [hb.2.2]
  have hbudget : 0 ≤ (17*D+3*Dβ+60)*Real.log m := hB.trans hlog
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hAp : 0 < accuracyScale out.depth := lt_of_lt_of_le (by norm_num) (family_accuracyScale_ge_one _)
  have hi := family_inverse_accuracy_sqrt_bound s (accuracyScale out.depth) out.terminal hs hAp hp
    (out.nonzero_terminal_bounds hs hL).2.le
  change 1/Real.sqrt (familyOuterAccuracy out) ≤ 32*Real.sqrt (accuracyScale out.depth)/s^2 at hi
  have hsq := family_accuracyScale_sqrt_bound out.depth
  have hi' : 1/Real.sqrt (familyOuterAccuracy out) ≤ 224000*(10 : ℝ)^out.depth/s^2 := by
    apply hi.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg s)
    linarith
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)) hi'
    (by positivity : 0 ≤ 1/Real.sqrt (familyOuterAccuracy out)) (by nlinarith)
  calc
    _ ≤ 2*Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out)/
        Real.sqrt (familyOuterAccuracy out)+1 := hu
    _ ≤ (2*((17*D+3*Dβ+60)*Real.log m))*(224000*(10 : ℝ)^out.depth/s^2)+1 := by
      have he : 2*Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out)/
          Real.sqrt (familyOuterAccuracy out) =
        (2*Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out))*
          (1/Real.sqrt (familyOuterAccuracy out)) := by ring
      rw [he]
      exact add_le_add hprod (le_refl _)
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
