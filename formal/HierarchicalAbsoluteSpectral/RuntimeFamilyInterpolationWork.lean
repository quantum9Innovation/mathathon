import HierarchicalAbsoluteSpectral.RuntimeFamilyUniformDegrees
import HierarchicalAbsoluteSpectral.AutomaticPolynomial

/-! The logarithmic interpolation level also bounds the literal scalar
coefficient-generation work, uniformly over every accepted schedule level. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

def familyInterpolationConstant (D : ℝ) : ℝ := 17000*(3*D+21)
def familyInterpolationLevelConstant (D : ℝ) : ℝ :=
  (D+Real.log (familyInterpolationConstant D)+1)/Real.log 2

theorem family_uniform_interpolation_level {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hD : 1 ≤ D) (hm : 1 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (j : ℕ) (hj : j < out.depth) :
    let H := familyScheduleValue (1/1024) (s/1024) j
    let h := familyScheduleValue (1/1024) (s/1024) (j+1)
    let η := 8*(h/H)
    let τ := h/(1000000*(1+(2 : ℝ)^(j+1)))
    ∃ (hη : 0 < η) (hη1 : η ≤ 1/8) (hτ : 0 < τ) (hτ1 : τ < 1/4),
      (inverseRootLevel η τ hη hτ : ℝ) ≤ familyInterpolationLevelConstant D*Real.log m ∧
      (2^inverseRootLevel η τ hη hτ : ℝ) ≤ familyInterpolationConstant D*(H/h)*Real.log m := by
  let H := familyScheduleValue (1/1024) (s/1024) j
  let h := familyScheduleValue (1/1024) (s/1024) (j+1)
  let η := 8*(h/H)
  let τ := h/(1000000*(1+(2 : ℝ)^(j+1)))
  have hm2 : Real.log 2 ≤ Real.log m := by
    have hl2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact hl2.trans hm
  obtain ⟨hη,hη1,hτ,hτ1,hu⟩ := family_uniform_interpolation_degree hs out hL hm2 hscale j hj
  have hH : 0 < H := familyScheduleValue_pos _ _ (by norm_num) (by positivity) j
  have hh : 0 < h := familyScheduleValue_pos _ _ (by norm_num) (by positivity) (j+1)
  have hbH := out.level_bounds hs hL j (by omega)
  have hbh := out.level_bounds hs hL (j+1) (by omega)
  have hK : 1 ≤ familyInterpolationConstant D := by unfold familyInterpolationConstant; linarith
  have hK0 : 0 < familyInterpolationConstant D := by linarith
  have hlogK : 0 ≤ Real.log (familyInterpolationConstant D) := Real.log_nonneg hK
  have hlogm0 : 0 < Real.log m := by linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2^inverseRootLevel η τ hη hτ) hu
  change Real.log ((2 : ℝ)^inverseRootLevel η τ hη hτ) ≤
    Real.log (familyInterpolationConstant D*(H/h)*Real.log m) at hl
  rw [Real.log_pow,Real.log_mul (by positivity) hlogm0.ne',
    Real.log_mul hK0.ne' (div_pos hH hh).ne',Real.log_div hH.ne' hh.ne'] at hl
  have hlogH : Real.log H ≤ 0 := Real.log_nonpos hH.le (by linarith [hbH.2])
  have hlogh := Real.log_le_log hs hbh.1
  have hslog : Real.log (1/s) = -Real.log s := by rw [one_div,Real.log_inv]
  rw [hslog] at hscale
  have hloglog := Real.log_le_sub_one_of_pos hlogm0
  have hKscale := mul_nonneg hlogK (sub_nonneg.mpr hm)
  refine ⟨hη,hη1,hτ,hτ1,?_,hu⟩
  have htarget : familyInterpolationLevelConstant D*Real.log m =
      ((D+Real.log (familyInterpolationConstant D)+1)*Real.log m)/Real.log 2 := by
    unfold familyInterpolationLevelConstant
    ring
  rw [htarget]
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  nlinarith

theorem family_interpolation_preparation_bound (D H h ell : ℝ) (n : ℕ)
    (hD : 1 ≤ D) (hH : 0 < H) (hh : 0 < h) (hell : 1 ≤ ell)
    (hlevel : (n : ℝ) ≤ familyInterpolationLevelConstant D*ell)
    (hdegree : (2^n : ℝ) ≤ familyInterpolationConstant D*(H/h)*ell) :
    80*((n : ℝ)+3)*2^n ≤
      (80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D)*(H/h)*ell^2 := by
  have hK : 0 < familyInterpolationConstant D := by unfold familyInterpolationConstant; linarith
  have hLC : 0 ≤ familyInterpolationLevelConstant D := by
    unfold familyInterpolationLevelConstant
    have hlog : 0 ≤ Real.log (familyInterpolationConstant D) := by
      apply Real.log_nonneg
      unfold familyInterpolationConstant
      linarith
    positivity
  have hlevel' : (n : ℝ)+3 ≤ (familyInterpolationLevelConstant D+3)*ell := by nlinarith
  have hp := mul_le_mul hlevel' hdegree (by positivity : (0 : ℝ) ≤ 2^n) (by positivity)
  have h80 := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 80)
  calc
    _ = 80*(((n : ℝ)+3)*2^n) := by ring
    _ ≤ 80*(((familyInterpolationLevelConstant D+3)*ell)*
      (familyInterpolationConstant D*(H/h)*ell)) := h80
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
