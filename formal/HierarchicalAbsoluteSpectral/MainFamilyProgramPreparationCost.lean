import HierarchicalAbsoluteSpectral.MainFamilyProgramWorkScales
import HierarchicalAbsoluteSpectral.MainSketchCost

/-! The actual initial sketch row sizes and complete fast-sketch formation
charge, with constants depending only on the family logarithmic budgets. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def familyCoarseRowCoefficient (D c : ℝ) : ℝ := 1048576*familyRowCoefficient D c
def familyPaddingCoefficient (D : ℝ) : ℝ := 2+(2*D+1)/Real.log 2
def familySketchFormationCoefficient (D c : ℝ) : ℝ :=
  128*familyPaddingCoefficient D+3*((c+2*D+10)/Real.log 2)+20

theorem PreparedFamilyProblem.actual_initial_rows_scale (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed) :
    let S := (mainSketchProgram P.fixed g).eval
    ((S.levelA 0).1 : ℝ) ≤ familyCoarseRowCoefficient D c*(m : ℝ)*(Real.log (m : ℝ))^3 ∧
      ((S.levelB 0).1 : ℝ) ≤ familyCoarseRowCoefficient D c*(m : ℝ)*(Real.log (m : ℝ))^3 := by
  intro S
  have hb := P.actual_sketch_rows_scale I hL D c hD hc hm hmLog hscale hδ g 0
  dsimp only at hb
  simp only [Fin.val_zero] at hb
  rw [P.normal_initial I hL] at hb
  norm_num [div_eq_mul_inv] at hb
  constructor
  · simpa only [S,familyCoarseRowCoefficient,mul_assoc,mul_comm,mul_left_comm] using hb.1
  · simpa only [S,familyCoarseRowCoefficient,mul_assoc,mul_comm,mul_left_comm] using hb.2

theorem familyPadding_log_bound (I : FamilyProblem N m r) (D : ℝ)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    ((dyadicPaddingLevel N+1 : ℕ) : ℝ) ≤ familyPaddingCoefficient D*Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hN0 : (0 : ℝ) < N := by exact_mod_cast I.side_positive
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from I.side_positive)
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogN : Real.log (N : ℝ) ≤ (2*D+1)*Real.log (m : ℝ) := by
    rw [family_ratio_log _ _ hm0 hN0] at hscale
    nlinarith
  have hu := leastHalvings_log_bound (N : ℝ) 1 (by norm_num)
  change (dyadicPaddingLevel N : ℝ) ≤ 1+Real.log (max 1 ((N : ℝ)/1))/Real.log 2 at hu
  simp only [div_one,max_eq_right hN1] at hu
  have hdiv := div_le_div_of_nonneg_right hlogN hlog2.le
  push_cast
  calc
    _ ≤ 2+Real.log (N : ℝ)/Real.log 2 := by linarith
    _ ≤ 2+((2*D+1)*Real.log (m : ℝ))/Real.log 2 := add_le_add (le_rfl : (2 : ℝ) ≤ 2) hdiv
    _ ≤ 2*Real.log (m : ℝ)+((2*D+1)*Real.log (m : ℝ))/Real.log 2 := by linarith
    _ = _ := by unfold familyPaddingCoefficient; ring

theorem PreparedFamilyProblem.embedding_order_scale (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hm : 2 ≤ m) (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (embeddingMomentOrder m P.fixed.sketchFailure : ℝ) ≤
      ((c+2*D+10)/Real.log 2)*Real.log (m : ℝ) := by
  have hβ : 0 < P.fixed.sketchFailure := by
    unfold FixedProblem.sketchFailure
    exact div_pos P.fixed.delta_positive (by positivity)
  have hβ1 : P.fixed.sketchFailure ≤ 1 := by
    unfold FixedProblem.sketchFailure
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := P.fixed.delta_lt_one
    have hdep : (0 : ℝ) ≤ P.depth := Nat.cast_nonneg _
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hb := family_embedding_order_uniform_bound m P.fixed.sketchFailure (c+5+2*D) hm hβ hβ1
    (P.sketchFailure_log_bound I hL D c (hlog2.trans hmLog) hscale hδ)
  simpa only [show c+5+2*D+5 = c+2*D+10 by ring] using hb

theorem PreparedFamilyProblem.sketch_formation_cap_scale (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (sketchFormationCap N m P.fixed.sketchFailure : ℝ) ≤
      familySketchFormationCoefficient D c*(N : ℝ)*(m : ℝ)*Real.log (m : ℝ) := by
  have hraw := sketchFormationCap_input_bound N m P.fixed.sketchFailure I.side_positive I.core_positive
  have hrawR : (sketchFormationCap N m P.fixed.sketchFailure : ℝ) ≤
      128*(m : ℝ)*((dyadicPaddingLevel N+1 : ℕ) : ℝ)*(N : ℝ)+
        3*(embeddingMomentOrder m P.fixed.sketchFailure : ℝ)+20 := by exact_mod_cast hraw
  have hpad := familyPadding_log_bound I D hmLog hscale
  have hmoment := P.embedding_order_scale I hL D c hm hmLog hscale hδ
  have hM1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m from I.core_positive)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from I.side_positive)
  have hMN : 1 ≤ (N : ℝ)*(m : ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (sub_nonneg.mpr hM1)]
  have hMNlog : 1 ≤ (N : ℝ)*(m : ℝ)*Real.log (m : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMN) (show 0 ≤ Real.log (m : ℝ)-1 by linarith)]
  have hK : 0 ≤ (c+2*D+10)/Real.log 2 := by positivity
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpad
    (show 0 ≤ 128*(m : ℝ) by positivity)) (Nat.cast_nonneg N)
  have hextra := mul_le_mul_of_nonneg_left hMN
    (show 0 ≤ 3*((c+2*D+10)/Real.log 2)*Real.log (m : ℝ) by positivity)
  have htwenty := mul_le_mul_of_nonneg_left hMNlog (by norm_num : (0 : ℝ) ≤ 20)
  calc
    _ ≤ 128*(m : ℝ)*((dyadicPaddingLevel N+1 : ℕ) : ℝ)*(N : ℝ)+
        3*(embeddingMomentOrder m P.fixed.sketchFailure : ℝ)+20 := hrawR
    _ ≤ 128*(m : ℝ)*(familyPaddingCoefficient D*Real.log (m : ℝ))*(N : ℝ)+
        3*(((c+2*D+10)/Real.log 2)*Real.log (m : ℝ))+20 :=
      add_le_add (add_le_add hmain (mul_le_mul_of_nonneg_left hmoment (by norm_num))) le_rfl
    _ ≤ 128*(m : ℝ)*(familyPaddingCoefficient D*Real.log (m : ℝ))*(N : ℝ)+
        (3*((c+2*D+10)/Real.log 2)*Real.log (m : ℝ))*((N : ℝ)*(m : ℝ))+
          20*((N : ℝ)*(m : ℝ)*Real.log (m : ℝ)) := by
      have he : 3*(((c+2*D+10)/Real.log 2)*Real.log (m : ℝ)) ≤
          (3*((c+2*D+10)/Real.log 2)*Real.log (m : ℝ))*((N : ℝ)*(m : ℝ)) := by
        simpa only [one_mul,mul_one,mul_assoc] using hextra
      exact add_le_add (add_le_add (le_rfl : _ ≤ _) he) (by simpa only [mul_one] using htwenty)
    _ = _ := by unfold familySketchFormationCoefficient; ring

end
end HierarchicalAbsoluteSpectral
