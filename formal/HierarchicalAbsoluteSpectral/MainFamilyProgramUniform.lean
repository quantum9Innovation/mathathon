import HierarchicalAbsoluteSpectral.MainFamilyProgramDegrees
import HierarchicalAbsoluteSpectral.MainFamilyProgramGrowth

/-! The actual query degree fits the manuscript's raw-width condition
eventually, uniformly over all computed supports and all random outcomes. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
variable {N m r : ℕ}

def familyQueryDegreeCeiling (I : FamilyProblem N m r) (D : ℝ) : ℕ :=
  ⌈familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1⌉₊

theorem familyQueryDegreeCeiling_bound (I : FamilyProblem N m r)
    (D : ℝ) (hD : 0 ≤ D) (hm : 1 ≤ Real.log (m : ℝ)) :
    (familyQueryDegreeCeiling I D : ℝ) ≤
      (familyQueryDegreeCoefficient D+1)*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hratio : 1 ≤ (N : ℝ)/m := (le_div_iff₀ hm0).mpr
    (by simpa only [one_mul] using (show (m : ℝ) ≤ N by exact_mod_cast I.core_le_side))
  have hlog : 1 ≤ (Real.log (m : ℝ))^5 := one_le_pow₀ hm
  have hprod : 1 ≤ ((N : ℝ)/m)*(Real.log (m : ℝ))^5 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hlog)]
  have hC : 0 ≤ familyQueryDegreeCoefficient D := by unfold familyQueryDegreeCoefficient; positivity
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤
    familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 by positivity)).le
  change (familyQueryDegreeCeiling I D : ℝ) ≤ _ at hceil
  nlinarith

theorem PreparedFamilyProblem.mainKrylov_degree_le_ceiling (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hr : r < C.pair.dimension)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    mainKrylovDegree P.fixed S C hr ≤ familyQueryDegreeCeiling I D := by
  have hq := P.mainKrylov_degree_polylog I hL S C hr D hD hm hscale
  have hceil := Nat.le_ceil (familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1)
  exact_mod_cast hq.trans hceil

theorem familyProgram_sequence_raw_width {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d : ℝ) (hd : FamilyExponentAdmissible d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      (2*familyQueryDegreeCeiling (I i) D+1)*(r i+1) < m i ∧
      ∀ (S : StoredSketches (N i) (m i) (N i) (I i).prepared.depth) (C : MainSupportData S)
        (hr : r i < C.pair.dimension),
        (2*mainKrylovDegree (I i).prepared.fixed S C hr+1)*(r i+1) < m i := by
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd.positive hm
    (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1 : ℝ))
  have hC : 0 ≤ familyQueryDegreeCoefficient D+1 := by
    unfold familyQueryDegreeCoefficient
    have : 0 ≤ D := by linarith
    positivity
  have hqpoly : ∀ᶠ i in l, (familyQueryDegreeCeiling (I i) D : ℝ) ≤
      (familyQueryDegreeCoefficient D+1)*((N i : ℝ)/m i)*(Real.log (m i : ℝ))^5+1 := by
    filter_upwards [hmLog] with i hi
    exact familyQueryDegreeCeiling_bound (I i) D (by linarith) hi
  have hq := family_degree_sequence_subpolynomial_slack l m N
    (fun i => familyQueryDegreeCeiling (I i) D) d (familyQueryDegreeCoefficient D+1) hd.positive hC
    hm (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth hqpoly
  have hrank : ∀ᶠ i in l, (r i : ℝ) ≤ Real.sqrt (m i : ℝ) := Eventually.of_forall (fun i => by
    exact (by exact_mod_cast (I i).rank_le_sqrt : (r i : ℝ) ≤ ⌊Real.sqrt (m i : ℝ)⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg _)))
  have hraw := family_raw_width_sequence l m (fun i => familyQueryDegreeCeiling (I i) D) r d hd hm hq hrank
  refine ⟨D,hD,?_⟩
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  filter_upwards [hraw,hscale,hmLog,
    familyPreparationProgram_eventually_normal l m N r I d hd.positive hm hgrowth]
    with i hrawi hscalei hlogmi hnormal
  refine ⟨hrawi,?_⟩
  intro S C hr
  have hnormal' : (I i).prepared.scalars.schedule.depth ≠ 0 := by
    rw [familyPreparationProgram_scalars]
    exact hnormal.ne'
  have hdegree := (I i).prepared.mainKrylov_degree_le_ceiling (I i) hnormal' S C hr D
    (by linarith) (hlog2.trans hlogmi) hscalei.2
  have hwidth : (2*mainKrylovDegree (I i).prepared.fixed S C hr+1)*(r i+1) ≤
      (2*familyQueryDegreeCeiling (I i) D+1)*(r i+1) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdegree) 1)
  exact hwidth.trans_lt hrawi

end
end HierarchicalAbsoluteSpectral
