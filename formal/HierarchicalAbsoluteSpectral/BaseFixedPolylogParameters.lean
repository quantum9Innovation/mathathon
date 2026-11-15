import HierarchicalAbsoluteSpectral.BaseFixedPolylogBasic

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedPolylogAlphaScale (L : ℕ) : ℝ := 1000000*(hierarchyConstant L+1)
def fixedPolylogFineCoefficient (L : ℕ) : ℝ := 1+401*(L:ℝ)
def fixedPolylogRefinementCoefficient (L : ℕ) : ℝ :=
  1+(L:ℝ)*(1000002+hierarchyUpper L)
def fixedPolylogTrueCoefficient (L : ℕ) : ℝ := 5+4*fixedPolylogAlphaScale L

theorem fixedPolylogAlphaScale_ge_one (L : ℕ) : 1 ≤ fixedPolylogAlphaScale L := by
  have hh := hierarchyConstant_ge_one L
  unfold fixedPolylogAlphaScale
  linarith

theorem fixedPolylog_baseLog_bound (I : FixedProblem n m p r L) :
    baseFixedInitialLog I ≤ 5*fixedPolylogGauge I := by
  have hh := I.accuracy_positive 0 (by omega)
  have harg : 1/(4*I.accuracy 0) ≤ 1/I.accuracy 0 :=
    one_div_le_one_div_of_le hh (by linarith)
  have hl := Real.log_le_log (by positivity : 0<1/(4*I.accuracy 0)) harg
  have hH := fixedPolylog_accuracy_log_le I 0 (by omega)
  have hz := fixedPolylogGauge_ge_one I
  unfold baseFixedInitialLog
  linarith

theorem fixedPolylog_alpha_log_bound (I : FixedProblem n m p r L) :
    Real.log (1/I.alpha) ≤ (fixedPolylogAlphaScale L+1)*fixedPolylogGauge I := by
  have hA := fixedPolylogAlphaScale_ge_one L
  have hAp : 0 < fixedPolylogAlphaScale L := by linarith
  have hH := I.accuracy_positive L le_rfl
  have hH1 : I.accuracy L ≤ 1 := by linarith [I.accuracy_bounded L le_rfl]
  have hhlog : Real.log (I.accuracy L) ≤ 0 := Real.log_nonpos hH.le hH1
  have ht := (fixedPolylog_primitive_le I).2.2.2.1
  have hz := fixedPolylogGauge_ge_one I
  have hconst := Real.log_le_sub_one_of_pos hAp
  have hconst' := mul_le_mul_of_nonneg_left hz hAp.le
  have he : Real.log (1/I.alpha) = Real.log (fixedPolylogAlphaScale L)+
      Real.log (I.accuracy L)+Real.log (1/I.theta) := by
    change Real.log (1/(I.theta/(fixedPolylogAlphaScale L*I.accuracy L))) = _
    rw [one_div,Real.log_inv,Real.log_div I.theta_positive.ne' (mul_pos hAp hH).ne',
      Real.log_mul hAp.ne' hH.ne',one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith only [hhlog,ht,hconst,hconst']

theorem fixedPolylog_trueLog_bound (I : FixedProblem n m p r L) :
    fixedTrueNeumannLog I ≤ fixedPolylogTrueCoefficient L*fixedPolylogGauge I := by
  have hA := fixedPolylogAlphaScale_ge_one L
  have hAp : 0 < fixedPolylogAlphaScale L := by linarith
  have hz := fixedPolylogGauge_ge_one I
  have ht := (fixedPolylog_primitive_le I).2.2.2.1
  have hconst := Real.log_le_sub_one_of_pos hAp
  have hconst' := mul_le_mul_of_nonneg_left hz hAp.le
  have he : Real.log (1/I.massAccuracy) =
      Real.log (fixedPolylogAlphaScale L)+Real.log (1/I.theta) := by
    change Real.log (1/(I.theta/fixedPolylogAlphaScale L)) = _
    rw [one_div,Real.log_inv,Real.log_div I.theta_positive.ne' hAp.ne',one_div,Real.log_inv]
    ring
  unfold fixedTrueNeumannLog fixedPolylogTrueCoefficient
  rw [he]
  nlinarith only [ht,hconst,hconst',hz]

theorem fixedPolylog_fineLog_bound (I : FixedProblem n m p r L) :
    fixedFineLog I ≤ fixedPolylogFineCoefficient L*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  have hterm (j : Fin L) : mainFineNeumannLog I j.val ≤ 401*fixedPolylogGauge I := by
    have hh := I.accuracy_positive (j.val+1) (by omega)
    have hl := fixedPolylog_accuracy_log_le I (j.val+1) (by omega)
    have he : Real.log (1/(safeAccuracy I (j.val+1)/100)) =
        Real.log 100+Real.log (1/I.accuracy (j.val+1)) := by
      rw [safeAccuracy_eq I (j.val+1) (by omega),one_div,Real.log_inv,
        Real.log_div hh.ne' (by norm_num),one_div,Real.log_inv]
      ring
    unfold mainFineNeumannLog
    rw [he]
    linarith
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin L))) (fun j _ => hterm j)
  have hs' : (∑ j : Fin L, mainFineNeumannLog I j.val) ≤ (L:ℝ)*(401*fixedPolylogGauge I) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs
  unfold fixedFineLog fixedPolylogFineCoefficient
  nlinarith only [hs',hz]

theorem fixedPolylog_refinementLog_bound (I : FixedProblem n m p r L) :
    fixedRefinementLog I ≤ fixedPolylogRefinementCoefficient L*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hBL := hierarchyUpper_nonneg L
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1000000)
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hterm (j : Fin L) : refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
      (I.accuracy (j.val+1)) (hierarchyUpper j.val) ≤
        (1000002+hierarchyUpper L)*fixedPolylogGauge I := by
    have hH := I.accuracy_positive j.val (by omega)
    have hh := I.accuracy_positive (j.val+1) (by omega)
    have hB := hierarchyUpper_nonneg j.val
    have hB' : hierarchyUpper j.val ≤ hierarchyUpper L := by
      unfold hierarchyUpper
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega)
    have hl := fixedPolylog_accuracy_log_le I (j.val+1) (by omega)
    have hHlog : Real.log (I.accuracy j.val) ≤ 0 :=
      Real.log_nonpos hH.le (by linarith [I.accuracy_bounded j.val (by omega)])
    have hBlog : Real.log (1+hierarchyUpper j.val) ≤ hierarchyUpper j.val := by
      have he := Real.log_le_sub_one_of_pos (by positivity : 0<1+hierarchyUpper j.val)
      linarith
    have he : refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
        (I.accuracy (j.val+1)) (hierarchyUpper j.val) =
      Real.log 1000000+Real.log (1+hierarchyUpper j.val)-Real.log 8+
        Real.log (I.accuracy j.val)+2*Real.log (1/I.accuracy (j.val+1)) := by
      unfold refinementLogBudget refinementTolerance
      rw [one_div,Real.log_inv,Real.log_mul (by positivity) (by positivity),
        Real.log_div hh.ne' (by positivity),Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (div_pos hh hH).ne',Real.log_div hh.ne' hH.ne',
        one_div,Real.log_inv]
      ring
    rw [he]
    have hconst := mul_le_mul_of_nonneg_left hz (show 0≤1000000+hierarchyUpper L by positivity)
    nlinarith only [hc,hBlog,hB',h8,hHlog,hl,hconst]
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin L))) (fun j _ => hterm j)
  have hs' : (∑ j : Fin L, refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
      (I.accuracy (j.val+1)) (hierarchyUpper j.val)) ≤
        (L:ℝ)*((1000002+hierarchyUpper L)*fixedPolylogGauge I) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs
  unfold fixedRefinementLog fixedPolylogRefinementCoefficient
  nlinarith only [hs',hz]

end
end HierarchicalAbsoluteSpectral
