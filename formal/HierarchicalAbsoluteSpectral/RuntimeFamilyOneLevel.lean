import HierarchicalAbsoluteSpectral.RuntimeFamilyInterpolationWork
import HierarchicalAbsoluteSpectral.CompiledHierarchy

/-! The literal compiled refinement envelope satisfies the uniform action
recurrence. Scalar table construction is charged on every invocation. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

def familyActionCostConstant (D : ℝ) : ℝ :=
  80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D+
    6*familyInterpolationConstant D+7

theorem familyActionCostConstant_ge_one (D : ℝ) (hD : 1 ≤ D) :
    1 ≤ familyActionCostConstant D := by
  have hK : 1 ≤ familyInterpolationConstant D := by unfold familyInterpolationConstant; linarith
  have hlog : 0 ≤ Real.log (familyInterpolationConstant D) := Real.log_nonneg hK
  have hlevel : 0 ≤ familyInterpolationLevelConstant D := by
    unfold familyInterpolationLevelConstant
    positivity
  unfold familyActionCostConstant
  have hp : 0 ≤ 80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D := by positivity
  linarith

theorem family_refinement_envelope_bound {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hD : 1 ≤ D) (hm : 1 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (j : ℕ) (hj : j < out.depth) (P T J k b : ℕ) :
    let H := familyScheduleValue (1/1024) (s/1024) j
    let h := familyScheduleValue (1/1024) (s/1024) (j+1)
    let ε := h/H
    let B := (2 : ℝ)^(j+1)
    ∃ (hε : 0 < ε) (hh : 0 < h) (hB : 0 ≤ B),
      (refinementActionEnvelope P T J ε h B hε hh hB k b : ℝ) ≤
      familyActionCostConstant D*(H/h)*(Real.log m)^2*
        ((P : ℝ)+(T : ℝ)+(J : ℝ)+(k : ℝ)*b+1) := by
  let H := familyScheduleValue (1/1024) (s/1024) j
  let h := familyScheduleValue (1/1024) (s/1024) (j+1)
  let R := H/h
  let ell := Real.log m
  let W : ℝ := (P : ℝ)+(T : ℝ)+(J : ℝ)+(k : ℝ)*b+1
  have hH : 0 < H := familyScheduleValue_pos _ _ (by norm_num) (by positivity) j
  have hh : 0 < h := familyScheduleValue_pos _ _ (by norm_num) (by positivity) (j+1)
  have hε : 0 < h/H := div_pos hh hH
  have hB : 0 ≤ (2 : ℝ)^(j+1) := by positivity
  obtain ⟨hη,hη1,hτ,hτ1,hlevel,hdegree⟩ := family_uniform_interpolation_level hs out hL hD hm hscale j hj
  let n := inverseRootLevel (8*(h/H)) (h/(1000000*(1+(2 : ℝ)^(j+1)))) hη hτ
  have hlevel' : (n : ℝ) ≤ familyInterpolationLevelConstant D*ell := hlevel
  have hdegree' : (2^n : ℝ) ≤ familyInterpolationConstant D*R*ell := hdegree
  have hprep := family_interpolation_preparation_bound D H h ell n hD hH hh hm hlevel' hdegree'
  have hR : 1 ≤ R := by
    apply (le_div_iff₀ hh).mpr
    have ha := out.ratios j hj
    change h ≤ H/1024 at ha
    nlinarith
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hkb : (0 : ℝ) ≤ (k : ℝ)*b := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hW : 1 ≤ W := by
    dsimp [W]
    nlinarith
  have hell : 1 ≤ ell := hm
  have hK : 0 < familyInterpolationConstant D := by unfold familyInterpolationConstant; linarith
  have hLC : 0 ≤ familyInterpolationLevelConstant D := by
    unfold familyInterpolationLevelConstant
    have hk : 0 ≤ Real.log (familyInterpolationConstant D) := by
      apply Real.log_nonneg
      unfold familyInterpolationConstant
      linarith
    positivity
  have hRell : 1 ≤ R*ell^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (show 0 ≤ ell^2-1 by nlinarith)]
  have hdegree2 : (2^n : ℝ) ≤ familyInterpolationConstant D*R*ell^2 := by
    apply hdegree'.trans
    have he : ell ≤ ell^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hcount : (P : ℝ)+(T : ℝ)+(J : ℝ)+6*(k : ℝ)*b ≤ 6*W := by
    dsimp [W]
    nlinarith
  have hprod := mul_le_mul hdegree2 hcount (by positivity) (by positivity)
  have hbase : 7+max (P : ℝ) (T : ℝ)+(k : ℝ)*b ≤ 7*W := by
    have hn : 7+max P T+k*b ≤ 7*(P+T+J+k*b+1) := by omega
    dsimp only [W]
    exact_mod_cast hn
  have hbase2 : 7+max (P : ℝ) (T : ℝ)+(k : ℝ)*b ≤ 7*(R*ell^2)*W := by
    apply hbase.trans
    have hh' := mul_le_mul_of_nonneg_right hRell (by positivity : 0 ≤ 7*W)
    nlinarith
  have hprep2 : 80*((n : ℝ)+3)*2^n ≤
      (80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D)*R*ell^2*W := by
    apply hprep.trans
    have hh' := mul_nonneg
      (by positivity : 0 ≤ (80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D)*R*ell^2)
      (sub_nonneg.mpr hW)
    nlinarith
  refine ⟨hε,hh,hB,?_⟩
  change (refinementActionEnvelope P T J (h/H) h ((2 : ℝ)^(j+1)) hε hh hB k b : ℝ) ≤
    familyActionCostConstant D*R*ell^2*W
  have he : (refinementActionEnvelope P T J (h/H) h ((2 : ℝ)^(j+1)) hε hh hB k b : ℝ) =
      7+80*((n : ℝ)+3)*2^n+max (P : ℝ) (T : ℝ)+(k : ℝ)*b+
        2^n*((P : ℝ)+(T : ℝ)+(J : ℝ)+6*(k : ℝ)*b) := by
    unfold refinementActionEnvelope
    simp only [refinementTolerance,show (10 : ℝ)^6 = 1000000 by norm_num]
    change ((7+80*(n+3)*2^n+max P T+k*b+2^n*(P+T+J+6*k*b) : ℕ) : ℝ) = _
    push_cast
    ring
  rw [he]
  have htotal := add_le_add (add_le_add hbase2 hprep2) hprod
  calc
    _ = (7+max (P : ℝ) (T : ℝ)+(k : ℝ)*b)+80*((n : ℝ)+3)*2^n+
        2^n*((P : ℝ)+(T : ℝ)+(J : ℝ)+6*(k : ℝ)*b) := by ring
    _ ≤ 7*(R*ell^2)*W+
        (80*(familyInterpolationLevelConstant D+3)*familyInterpolationConstant D)*R*ell^2*W+
        (familyInterpolationConstant D*R*ell^2)*(6*W) := htotal
    _ = _ := by unfold familyActionCostConstant; ring

end
end HierarchicalAbsoluteSpectral
