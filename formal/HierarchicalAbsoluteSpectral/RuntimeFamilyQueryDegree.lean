import HierarchicalAbsoluteSpectral.RuntimeFamilyStrongDegree

/-! The threshold query uses accuracy α/100. Its actual computed degree
satisfies the same family bound with a fixed tenfold prefactor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

theorem gaussianDegree_scalar_bound (k : ℕ) (U β α E F : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hlog : Real.log (4*gaussianCaptureRadius k U β/α) ≤ E)
    (hinv : 1/Real.sqrt α ≤ F) :
    (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1 : ℝ) ≤ 2*E*F+1 := by
  have hR := gaussianCaptureRadius_ge_one k U β hk hU hβ hβ1
  have hB : 0 ≤ Real.log (4*gaussianCaptureRadius k U β/α) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hα).mpr (by linarith)
  have hE : 0 ≤ E := hB.trans hlog
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)) hinv
    (by positivity : 0 ≤ 1/Real.sqrt α) (by positivity : 0 ≤ 2*E)
  have hu := strongGaussianDegree_bound k U β α hk hU hβ hβ1 hα hα1
  have he : 2*Real.log (4*gaussianCaptureRadius k U β/α)/Real.sqrt α =
      (2*Real.log (4*gaussianCaptureRadius k U β/α))*(1/Real.sqrt α) := by ring
  rw [he] at hu
  exact hu.trans (add_le_add hprod (le_refl _))

theorem family_query_degree_uniform_bound {s m D Dβ β : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log m) :
    ∃ (hU : 1 ≤ familyCovarianceEnvelope out) (hα : 0 < familyOuterAccuracy out/100)
      (hα1 : familyOuterAccuracy out/100 ≤ 1),
      (strongGaussianDegree k (familyCovarianceEnvelope out) β (familyOuterAccuracy out/100)
        hk hU hβ hβ1 hα hα1 : ℝ) ≤
      4480000*(17*D+3*Dβ+70)*((10 : ℝ)^out.depth/s^2)*Real.log m+1 := by
  have hb := family_covariance_accuracy_bounds hs out hL
  have hα : 0 < familyOuterAccuracy out/100 := by positivity [hb.2.1]
  have hα1 : familyOuterAccuracy out/100 ≤ 1 := by linarith [hb.2.2]
  have hR := gaussianCaptureRadius_ge_one k (familyCovarianceEnvelope out) β hk hb.1 hβ hβ1
  have hlog := family_gaussian_log_budget hs out hL k hk hkm hβ hβ1 hD hm hscale hconfidence
  have h100 : Real.log (100 : ℝ) ≤ 7*Real.log 2 := by
    have hx := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ (2 : ℝ)^7)
    rwa [Real.log_pow] at hx
  have hlog100 : Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/
      (familyOuterAccuracy out/100)) ≤ (17*D+3*Dβ+70)*Real.log m := by
    have he : 4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/(familyOuterAccuracy out/100) =
        (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out)*100 := by ring
    rw [he,Real.log_mul (by positivity [hb.2.1]) (by norm_num)]
    have hm0 : 0 ≤ Real.log m := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hm
    nlinarith
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hAp : 0 < accuracyScale out.depth := lt_of_lt_of_le (by norm_num) (family_accuracyScale_ge_one _)
  have hi := family_inverse_accuracy_sqrt_bound s (accuracyScale out.depth) out.terminal hs hAp hp
    (out.nonzero_terminal_bounds hs hL).2.le
  change 1/Real.sqrt (familyOuterAccuracy out) ≤ 32*Real.sqrt (accuracyScale out.depth)/s^2 at hi
  have hi' : 1/Real.sqrt (familyOuterAccuracy out) ≤ 224000*(10 : ℝ)^out.depth/s^2 := by
    apply hi.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg s)
    linarith [family_accuracyScale_sqrt_bound out.depth]
  have hroot : Real.sqrt (familyOuterAccuracy out/100) = Real.sqrt (familyOuterAccuracy out)/10 := by
    rw [Real.sqrt_div hb.2.1.le]
    norm_num
  have hi100 : 1/Real.sqrt (familyOuterAccuracy out/100) ≤ 2240000*(10 : ℝ)^out.depth/s^2 := by
    rw [hroot]
    have he : 1/(Real.sqrt (familyOuterAccuracy out)/10) = 10*(1/Real.sqrt (familyOuterAccuracy out)) := by ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hi' (by norm_num : (0 : ℝ) ≤ 10)
    exact hh.trans_eq (by ring)
  refine ⟨hb.1,hα,hα1,?_⟩
  have hu := gaussianDegree_scalar_bound k (familyCovarianceEnvelope out) β (familyOuterAccuracy out/100)
    ((17*D+3*Dβ+70)*Real.log m) (2240000*(10 : ℝ)^out.depth/s^2)
    hk hb.1 hβ hβ1 hα hα1 hlog100 hi100
  convert hu using 1 <;> ring

end
end HierarchicalAbsoluteSpectral
