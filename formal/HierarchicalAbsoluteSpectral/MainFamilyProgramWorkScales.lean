import HierarchicalAbsoluteSpectral.MainFamilyProgramSketchRows

/-! Explicit row envelopes and the square-root schedule identity which
cancels every fine-level row-size factor in the weighted action recurrence. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def familyRowCoefficient (D c : ℝ) : ℝ :=
  1+8192*(1+27*((c+2*D+10)/Real.log 2)^3)

theorem familyRowCoefficient_ge_one (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) :
    1 ≤ familyRowCoefficient D c := by
  unfold familyRowCoefficient
  have hlog2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hp : 0 ≤ 8192*(1+27*((c+2*D+10)/Real.log 2)^3) := by positivity
  linarith

theorem family_row_envelope_scale (M h ell K : ℝ) (hM : 1 ≤ M) (hh : 0 < h)
    (hh1 : h ≤ 1) (hell : 1 ≤ ell) (hK : 0 ≤ K) :
    1+8192*(M+27*(K*ell)^3)/h^2 ≤
      (1+8192*(1+27*K^3))*M*ell^3/h^2 := by
  have hpow : 1 ≤ ell^3 := one_le_pow₀ hell
  have hM0 : 0 ≤ M := by linarith
  have hnum : M+27*(K*ell)^3 ≤ (1+27*K^3)*M*ell^3 := by
    rw [mul_pow]
    have hfirst := mul_le_mul_of_nonneg_left hpow hM0
    have hsecond := mul_le_mul_of_nonneg_right hM (show 0 ≤ 27*K^3*ell^3 by positivity)
    nlinarith
  have hsq : 0 < h^2 := sq_pos_of_pos hh
  have hprod : 1 ≤ M*ell^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hpow)]
  have hone : 1 ≤ M*ell^3/h^2 := (le_div_iff₀ hsq).mpr (by nlinarith)
  calc
    _ ≤ M*ell^3/h^2+8192*((1+27*K^3)*M*ell^3)/h^2 :=
      add_le_add hone (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num)) hsq.le)
    _ = _ := by ring

theorem PreparedFamilyProblem.accuracy_le_initial (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (j : ℕ) (hj : j ≤ P.depth) : P.fixed.accuracy j ≤ 1/1024 := by
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hdepth := P.normal_depth I hL
  have hb := P.scalars.schedule_scale.level_bounds hs
    (by rw [← hdepth]; exact P.fixed.depth_positive) j (by omega)
  rw [← P.normal_accuracy_scale I hL j hj] at hb
  exact hb.2

theorem PreparedFamilyProblem.actual_sketch_rows_scale (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed) (j : Fin (P.depth+1)) :
    let bound := familyRowCoefficient D c*(m : ℝ)*(Real.log (m : ℝ))^3/(P.fixed.accuracy j.val)^2
    (((mainSketchProgram P.fixed g).eval.levelA j).1 : ℝ) ≤ bound ∧
      (((mainSketchProgram P.fixed g).eval.levelB j).1 : ℝ) ≤ bound := by
  intro bound
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hb := P.actual_sketch_rows_bound I hL D c hD hc hm (hlog2.trans hmLog) hscale hδ g j
  have hK : 0 ≤ (c+2*D+10)/Real.log 2 := by positivity
  have hr := family_row_envelope_scale (m : ℝ) (P.fixed.accuracy j.val) (Real.log (m : ℝ))
    ((c+2*D+10)/Real.log 2) (by exact_mod_cast (show 1 ≤ m by omega))
    (P.fixed.accuracy_positive j.val (by omega)) (by linarith [P.accuracy_le_initial I hL j.val (by omega)]) hmLog hK
  exact ⟨hb.1.trans hr,hb.2.trans hr⟩

theorem PreparedFamilyProblem.weighted_actual_fine_rows (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (j : ℕ) (hj : j < P.depth) :
    let S := (mainSketchProgram P.fixed g).eval
    P.fixed.accuracy j*
      (((S.levelA (safeSketchIndex P.depth (j+1))).1 : ℝ)+
        ((S.levelB (safeSketchIndex P.depth (j+1))).1 : ℝ)+(m : ℝ))*(m : ℝ) ≤
      3072*familyRowCoefficient D c*((m : ℝ)^2/Real.sqrt (m/N : ℝ))*(Real.log (m : ℝ))^3 := by
  intro S
  let H := P.fixed.accuracy j
  let h := P.fixed.accuracy (j+1)
  let ell := Real.log (m : ℝ)
  let E := familyRowCoefficient D c
  have hH : 0 < H := P.fixed.accuracy_positive j (by omega)
  have hh : 0 < h := P.fixed.accuracy_positive (j+1) (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hs := Real.sqrt_pos.mpr I.ratio_positive
  have hE : 1 ≤ E := familyRowCoefficient_ge_one D c hD hc
  have hE0 : 0 ≤ E := by linarith
  have hell : 1 ≤ ell := hmLog
  have hpow : 1 ≤ ell^3 := one_le_pow₀ hell
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [P.accuracy_le_initial I hL (j+1) (by omega)]
  have hb := P.actual_sketch_rows_scale I hL D c hD hc hm hmLog hscale hδ g
    (safeSketchIndex P.depth (j+1))
  simp only [safeSketchIndex,Nat.min_eq_left (show j+1 ≤ P.depth by omega)] at hb
  have hunit : (m : ℝ) ≤ E*(m : ℝ)*ell^3/h^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    have hx := mul_le_mul hE hpow (by norm_num : (0 : ℝ) ≤ 1) hE0
    have hx' := mul_le_mul_of_nonneg_right hx hm0.le
    have hy : h^2 ≤ 1 := by nlinarith
    have hy' := mul_le_mul_of_nonneg_left hy hm0.le
    nlinarith
  have hsum : (((S.levelA (safeSketchIndex P.depth (j+1))).1 : ℝ)+
      ((S.levelB (safeSketchIndex P.depth (j+1))).1 : ℝ)+(m : ℝ)) ≤
      3*E*(m : ℝ)*ell^3/h^2 := by
    change _ ≤ 3*E*(m : ℝ)*ell^3/h^2
    change _ ≤ E*(m : ℝ)*ell^3/h^2 ∧ _ ≤ E*(m : ℝ)*ell^3/h^2 at hb
    simp only [S,safeSketchIndex,Nat.min_eq_left (show j+1 ≤ P.depth by omega)]
    calc
      _ ≤ (E*(m : ℝ)*ell^3/h^2)+(E*(m : ℝ)*ell^3/h^2)+(E*(m : ℝ)*ell^3/h^2) :=
        add_le_add (add_le_add hb.1 hb.2) hunit
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hH.le) hm0.le
  have hstep : h^2 = H*(Real.sqrt (m/N : ℝ)/1024) := P.normal_square_step I hL j hj
  apply hmul.trans_eq
  rw [hstep]
  dsimp only [ell,E]
  field_simp [hH.ne',hs.ne']
  <;> ring

end
end HierarchicalAbsoluteSpectral
