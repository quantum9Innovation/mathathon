import HierarchicalAbsoluteSpectral.MainFamilyProgramUniform
import HierarchicalAbsoluteSpectral.BaseMainStrongCost

/-! One deterministic finite ceiling controls both actual filter degrees
and their raw Krylov widths on every support. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
variable {N m r : ℕ}

def familyStrongDegreeCeiling (I : FamilyProblem N m r) (D c : ℝ) : ℕ :=
  ⌈familyStrongDegreeCoefficient D (c+5)*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1⌉₊

def familyCombinedDegreeCeiling (I : FamilyProblem N m r) (D c : ℝ) : ℕ :=
  max (2*familyQueryDegreeCeiling I D) (familyStrongDegreeCeiling I D c)

def familyCombinedDegreeCoefficient (D c : ℝ) : ℝ :=
  2*familyQueryDegreeCoefficient D+familyStrongDegreeCoefficient D (c+5)+4

theorem PreparedFamilyProblem.mainStrong_degree_polylog (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (mainStrongDegree P.fixed S C hk : ℝ) ≤
      familyStrongDegreeCoefficient D (c+5)*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  unfold mainStrongDegree
  apply P.strong_degree_polylog I hL C.pair.dimension hk
    (by exact_mod_cast mainSupport_dimension_le S C) D (c+5) P.fixed.singleFailure
    (div_pos P.fixed.delta_positive (by norm_num))
    (by have hh := P.fixed.delta_lt_one; unfold FixedProblem.singleFailure; linarith)
    hD (by linarith) hm hscale (family_singleFailure_log_bound I P c hm hδ)
    (by have hh := P.fixed.final_budget.alpha_small; change P.fixed.alpha ≤ _ at hh; linarith)

theorem PreparedFamilyProblem.mainStrong_degree_le_ceiling (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    mainStrongDegree P.fixed S C hk ≤ familyStrongDegreeCeiling I D c := by
  have hh := P.mainStrong_degree_polylog I hL S C hk D c hD hc hm hscale hδ
  exact_mod_cast hh.trans (Nat.le_ceil _)

theorem PreparedFamilyProblem.combined_degree_bounds (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (∀ hr : r < C.pair.dimension, 2*mainQueryDegree P.fixed S C hr ≤ familyCombinedDegreeCeiling I D c) ∧
      (∀ hk : 1 ≤ C.pair.dimension, mainStrongDegree P.fixed S C hk ≤ familyCombinedDegreeCeiling I D c) := by
  constructor
  · intro hr
    have he : mainQueryDegree P.fixed S C hr = mainKrylovDegree P.fixed S C hr := rfl
    rw [he]
    exact (Nat.mul_le_mul_left 2 (P.mainKrylov_degree_le_ceiling I hL S C hr D hD hm hscale)).trans
      (le_max_left _ _)
  · intro hk
    exact (P.mainStrong_degree_le_ceiling I hL S C hk D c hD hc hm hscale hδ).trans (le_max_right _ _)

theorem familyCombinedDegreeCeiling_bound (I : FamilyProblem N m r)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hmLog : 1 ≤ Real.log (m : ℝ)) :
    (familyCombinedDegreeCeiling I D c : ℝ) ≤
      familyCombinedDegreeCoefficient D c*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  let X := ((N : ℝ)/m)*(Real.log (m : ℝ))^5
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hratio : 1 ≤ (N : ℝ)/m := (le_div_iff₀ hm0).mpr
    (by simpa only [one_mul] using (show (m : ℝ) ≤ N by exact_mod_cast I.core_le_side))
  have hlogpow : 1 ≤ (Real.log (m : ℝ))^5 := one_le_pow₀ hmLog
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hlogpow)]
  have hCq : 0 ≤ familyQueryDegreeCoefficient D := by unfold familyQueryDegreeCoefficient; positivity
  have hCs : 0 ≤ familyStrongDegreeCoefficient D (c+5) := by unfold familyStrongDegreeCoefficient; positivity
  have hq := familyQueryDegreeCeiling_bound I D hD hmLog
  have hs : (familyStrongDegreeCeiling I D c : ℝ) ≤
      (familyStrongDegreeCoefficient D (c+5)+1)*X+1 := by
    have he : familyStrongDegreeCeiling I D c = ⌈familyStrongDegreeCoefficient D (c+5)*X+1⌉₊ := by
      unfold familyStrongDegreeCeiling
      congr 1
      dsimp only [X]
      ring
    rw [he]
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ familyStrongDegreeCoefficient D (c+5)*X+1 by positivity)).le
    nlinarith
  have hq' : (familyQueryDegreeCeiling I D : ℝ) ≤ (familyQueryDegreeCoefficient D+1)*X+1 := by
    simpa only [X,mul_assoc] using hq
  unfold familyCombinedDegreeCeiling
  rw [Nat.cast_max,Nat.cast_mul,Nat.cast_ofNat]
  have hqX := mul_nonneg hCq (by linarith : 0 ≤ X)
  have hsX := mul_nonneg hCs (by linarith : 0 ≤ X)
  have hmax : max (2*(familyQueryDegreeCeiling I D : ℝ)) (familyStrongDegreeCeiling I D c : ℝ) ≤
      (2*familyQueryDegreeCoefficient D+familyStrongDegreeCoefficient D (c+5)+4)*X+1 :=
    max_le (by nlinarith [hq']) (by nlinarith)
  simpa only [familyCombinedDegreeCoefficient,X,mul_assoc] using hmax

theorem familyProgram_sequence_operational_parameters {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d c : ℝ) (hd : FamilyExponentAdmissible d) (hc : 0 ≤ c)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i : ℝ)^(-c) ≤ (I i).delta) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      let Q := familyCombinedDegreeCeiling (I i) D c
      Real.log (1/Real.sqrt (m i/N i : ℝ)) ≤ D*Real.log (m i : ℝ) ∧
      1 ≤ Real.log (m i : ℝ) ∧ (I i).prepared.scalars.schedule.depth ≠ 0 ∧
      (Q+1)*(r i+1) ≤ m i ∧
      ∀ (S : StoredSketches (N i) (m i) (N i) (I i).prepared.depth) (C : MainSupportData S),
        (∀ hr : r i < C.pair.dimension, mainQueryDegree (I i).prepared.fixed S C hr ≤ Q) ∧
        (∀ hk : 1 ≤ C.pair.dimension, mainStrongDegree (I i).prepared.fixed S C hk ≤ Q) := by
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd.positive hm
    (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1 : ℝ))
  have hC : 0 ≤ familyCombinedDegreeCoefficient D c := by
    unfold familyCombinedDegreeCoefficient familyQueryDegreeCoefficient familyStrongDegreeCoefficient
    have : 0 ≤ D := by linarith
    positivity
  have hqpoly : ∀ᶠ i in l, (familyCombinedDegreeCeiling (I i) D c : ℝ) ≤
      familyCombinedDegreeCoefficient D c*((N i : ℝ)/m i)*(Real.log (m i : ℝ))^5+1 := by
    filter_upwards [hmLog] with i hi
    exact familyCombinedDegreeCeiling_bound (I i) D c (by linarith) hc hi
  have hq := family_degree_sequence_subpolynomial_slack l m N
    (fun i => familyCombinedDegreeCeiling (I i) D c) d (familyCombinedDegreeCoefficient D c) hd.positive hC
    hm (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth hqpoly
  have hrank : ∀ᶠ i in l, (r i : ℝ) ≤ Real.sqrt (m i : ℝ) := Eventually.of_forall (fun i => by
    exact (by exact_mod_cast (I i).rank_le_sqrt : (r i : ℝ) ≤ ⌊Real.sqrt (m i : ℝ)⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg _)))
  have hraw := family_raw_width_sequence l m (fun i => familyCombinedDegreeCeiling (I i) D c) r d hd hm hq hrank
  refine ⟨D,hD,?_⟩
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  filter_upwards [hraw,hscale,hmLog,hδ,
    familyPreparationProgram_eventually_normal l m N r I d hd.positive hm hgrowth]
    with i hrawi hscalei hlogmi hδi hnormal
  have hnormal' : (I i).prepared.scalars.schedule.depth ≠ 0 := by
    rw [familyPreparationProgram_scalars]
    exact hnormal.ne'
  refine ⟨hscalei.2,hlogmi,hnormal',?_,?_⟩
  · have hw : (familyCombinedDegreeCeiling (I i) D c+1)*(r i+1) ≤
        (2*familyCombinedDegreeCeiling (I i) D c+1)*(r i+1) := Nat.mul_le_mul_right _ (by omega)
    exact hw.trans hrawi.le
  · intro S C
    have hb := (I i).prepared.combined_degree_bounds (I i) hnormal' S C D c
      (by linarith) hc (hlog2.trans hlogmi) hscalei.2 hδi
    exact ⟨fun hr => by have hh := hb.1 hr; omega,hb.2⟩

theorem familyProgram_sequence_combined_raw_width {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d c : ℝ) (hd : FamilyExponentAdmissible d) (hc : 0 ≤ c)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i : ℝ)^(-c) ≤ (I i).delta) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      let Q := familyCombinedDegreeCeiling (I i) D c
      (Q+1)*(r i+1) ≤ m i ∧
      ∀ (S : StoredSketches (N i) (m i) (N i) (I i).prepared.depth) (C : MainSupportData S),
        (∀ hr : r i < C.pair.dimension, mainQueryDegree (I i).prepared.fixed S C hr ≤ Q) ∧
        (∀ hk : 1 ≤ C.pair.dimension, mainStrongDegree (I i).prepared.fixed S C hk ≤ Q) := by
  obtain ⟨D,hD,hparams⟩ := familyProgram_sequence_operational_parameters l m N r I d c hd hc hm hgrowth hδ
  refine ⟨D,hD,?_⟩
  filter_upwards [hparams] with i hi
  exact hi.2.2.2

end
end HierarchicalAbsoluteSpectral
