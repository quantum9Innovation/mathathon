import HierarchicalAbsoluteSpectral.MainFamilyProgramParameters

/-! Quantified properties of the actual finite preparation, for arbitrary
integer dimension families with the manuscript's logarithmic growth law. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
variable {N m r : ℕ}

def FamilyExponentAdmissible (d : ℝ) : Prop :=
  (1/8 : ℝ) < d ∧ d < (Real.sqrt 2-1)/2

theorem FamilyExponentAdmissible.positive {d : ℝ} (hd : FamilyExponentAdmissible d) : 0 < d := by
  rcases hd with ⟨hlo,hhi⟩
  linarith

theorem FamilyExponentAdmissible.lt_half {d : ℝ} (hd : FamilyExponentAdmissible d) : d < 1/2 := by
  have hs : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  rcases hd with ⟨hlo,hhi⟩
  linarith

theorem familyScalarSchedule_no_level_finite_size (I : FamilyProblem N m r) (c : ℝ)
    (hc : 0 < c) (hz : I.scalarParameters.schedule.depth = 0)
    (hscale : c*Real.log (m : ℝ) ≤ Real.log (1/Real.sqrt (m/N : ℝ))) :
    (m : ℝ) < Real.exp (2*Real.log 1024/c) := by
  let out := I.scalarParameters
  have h : c*Real.log (m : ℝ) ≤ Real.log (1/out.scale) := by
    simpa only [out.scale_eq] using hscale
  change out.schedule.depth = 0 at hz
  rcases out with ⟨ρ,scale,ideal,theta,hρ,hscale,hideal,hθ,hs,hi,schedule⟩
  dsimp only at *
  subst ideal
  exact schedule.no_level_finite_size hs (by exact_mod_cast I.core_positive) hc hz h

theorem familyPreparationProgram_depth_loglog_bound (I : FamilyProblem N m r)
    (D : ℝ) (hD : 1 ≤ D) (hm : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    (I.prepared.depth : ℝ) ≤ 1+(Real.log D+Real.log (Real.log (m : ℝ)))/Real.log 2 := by
  have hs : 0 < Real.sqrt (m/N : ℝ)/1024 := by
    exact div_pos (Real.sqrt_pos.mpr I.ratio_positive) (by norm_num)
  have hlog : Real.log ((1/1024 : ℝ)/(Real.sqrt (m/N : ℝ)/1024)) ≤ D*Real.log (m : ℝ) := by
    convert hscale using 1
    congr 1
    field_simp
  have hb := familySchedule_depth_loglog_bound (1/1024) (Real.sqrt (m/N : ℝ)/1024)
    (m : ℝ) D (by norm_num) hs hD hm hlog
  have he : I.scalarParameters.schedule.depth =
      (familyScheduleProgram (1/1024) (Real.sqrt (m/N : ℝ)/1024) (by norm_num) hs).eval.depth :=
    familyScalarProgram_depth _ _ _ _
  rw [← he] at hb
  rw [familyPreparationProgram_depth]
  split_ifs with hz
  · simp only [Nat.cast_one]
    have hlogD := Real.log_nonneg hD
    have hloglog := Real.log_nonneg hm
    have hh := div_nonneg (add_nonneg hlogD hloglog) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    linarith
  · exact hb

theorem familyProgram_sequence_scale {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (d : ℝ) (hd : 0 < d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      (d/4)*Real.log (m i : ℝ) ≤ Real.log (1/Real.sqrt (m i/N i : ℝ)) ∧
      Real.log (1/Real.sqrt (m i/N i : ℝ)) ≤ D*Real.log (m i : ℝ) := by
  let D := max 1 (d+1)
  refine ⟨D,le_max_left _ _,?_⟩
  have hlo := family_sequence_dimension_powers l (fun i => (m i : ℝ)) (fun i => (N i : ℝ))
    d (d/2) (by positivity) hm (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth
  have hhi := family_sequence_dimension_powers l (fun i => (m i : ℝ)) (fun i => (N i : ℝ))
    d 1 (by norm_num) hm (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth
  filter_upwards [hlo,hhi,hN,hm.eventually (eventually_gt_atTop (1 : ℝ))] with i hlo hhi hN hm
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN
  have hl := family_ratio_log_bounds (m i : ℝ) (N i : ℝ) (d/2) (d+1) hm hNi
    (by convert hlo.1 using 1 <;> congr 1 <;> ring)
    (by convert hhi.2 using 1 <;> congr 1 <;> ring)
  refine ⟨by nlinarith [hl.1],hl.2.trans ?_⟩
  have hD : d+1 ≤ D := le_max_right _ _
  have hD1 : 1 ≤ D := le_max_left _ _
  have hlog := (Real.log_pos hm).le
  exact mul_le_mul_of_nonneg_right (by linarith : (d+1)/2 ≤ D) hlog

theorem familyPreparationProgram_eventually_normal {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d : ℝ) (hd : 0 < d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d))) :
    ∀ᶠ i in l, 0 < (I i).scalarParameters.schedule.depth := by
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd hm
    (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth
  filter_upwards [hscale,hm.eventually (eventually_ge_atTop (Real.exp (2*Real.log 1024/(d/4))))]
    with i hscale hlarge
  by_contra hn
  have hz : (I i).scalarParameters.schedule.depth = 0 := Nat.eq_zero_of_not_pos hn
  have hsmall := familyScalarSchedule_no_level_finite_size (I i) (d/4) (by positivity) hz hscale.1
  linarith

theorem familyProgram_confidence_log_bound (I : FamilyProblem N m r) (c : ℝ)
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    Real.log (1/I.delta) ≤ c*Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hδ
  rw [Real.log_rpow hm0] at hl
  rw [one_div,Real.log_inv]
  linarith

/-- The displayed interval is exactly the manuscript's interval. Every
conclusion concerns the problem constructed by the executed preparation. -/
theorem familyPreparationProgram_sequence_parameters {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d cδ : ℝ) (hd : FamilyExponentAdmissible d) (hcδ : 0 < cδ)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i : ℝ)^(-cδ) ≤ (I i).delta) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      (I i).prepared.depth = (I i).scalarParameters.schedule.depth ∧
      (I i).prepared.fixed.theta = (m i/N i : ℝ)^2*Real.sqrt (m i/N i : ℝ) ∧
      (I i).prepared.depth ≤ (I i).scalarParameters.schedule.depth ∧
      ((I i).prepared.depth : ℝ) ≤
        1+(Real.log D+Real.log (Real.log (m i : ℝ)))/Real.log 2 ∧
      Real.sqrt (m i/N i : ℝ) ≤ (I i).prepared.fixed.accuracy (I i).prepared.depth ∧
      (I i).prepared.fixed.accuracy (I i).prepared.depth < 1024*Real.sqrt (m i/N i : ℝ) ∧
      ((r i+1 : ℕ) : ℝ) ≤ 2*Real.sqrt (m i : ℝ) ∧
      r i+1 ≤ 2*⌈Real.sqrt (m i : ℝ)⌉₊ ∧
      Real.log (1/(I i).delta) ≤ cδ*Real.log (m i : ℝ) := by
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd.positive hm
    (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth
  refine ⟨D,hD,?_⟩
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hscale,familyPreparationProgram_eventually_normal l m N r I d hd.positive hm hgrowth,
    hmLog,hδ] with i hscale hnormal hmLog hδ
  have hnormal' : (I i).prepared.scalars.schedule.depth ≠ 0 := by
    rw [familyPreparationProgram_scalars]
    exact hnormal.ne'
  have he : (I i).prepared.depth = (I i).scalarParameters.schedule.depth := by
    rw [familyPreparationProgram_depth,if_neg hnormal.ne']
  have htheta := (I i).prepared.normal_theta hnormal'
  have hb := (I i).prepared.normal_terminal (I i) hnormal'
  have hr := (I i).rounded_rank_width
  exact ⟨he,htheta,he.le,familyPreparationProgram_depth_loglog_bound (I i) D hD hmLog hscale.2,
    hb.1,hb.2,by exact_mod_cast hr.1,hr.2,familyProgram_confidence_log_bound (I i) cδ hδ⟩

end
end HierarchicalAbsoluteSpectral
