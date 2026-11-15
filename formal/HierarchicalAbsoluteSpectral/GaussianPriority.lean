import HierarchicalAbsoluteSpectral.GaussianLinear
import HierarchicalAbsoluteSpectral.PrioritySortProgram
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fintype

/-! Gaussian priorities implement exact uniform sampling without replacement. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def PriorityRowSet (n M : ℕ) := {s : Finset (Fin n) // s.card = M}

instance priorityRowSet_fintype (n M : ℕ) : Fintype (PriorityRowSet n M) := by
  unfold PriorityRowSet
  infer_instance

instance priorityRowSet_measurableSpace (n M : ℕ) : MeasurableSpace (PriorityRowSet n M) := ⊤

instance priorityRowSet_measurableSingleton (n M : ℕ) : MeasurableSingletonClass (PriorityRowSet n M) := by
  constructor
  intro s
  trivial

def priorityRowSet (n M : ℕ) (hM : M ≤ n) (g : Fin n → ℝ) : PriorityRowSet n M :=
  ⟨priorityRows n M g, priorityRows_card n M hM g⟩

theorem priorityRowSet_nonempty (n M : ℕ) (hM : M ≤ n) : Nonempty (PriorityRowSet n M) :=
  ⟨priorityRowSet n M hM 0⟩

theorem priorityRowSet_measurable (n M : ℕ) (hM : M ≤ n) :
    Measurable (priorityRowSet n M hM) := by
  classical
  let table : (Fin n → ℝ) → Fin n → Fin n → Bool := fun g i j => decide (g i ≤ g j)
  have ht : Measurable table := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have he : (fun g : Fin n → ℝ => decide (g i ≤ g j)) =
        (fun g => if g i ≤ g j then true else false) := by
      funext g
      by_cases h : g i ≤ g j <;> simp [h]
    rw [he]
    exact Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
      measurable_const measurable_const
  let sample : (Fin n → Fin n → Bool) → PriorityRowSet n M := fun t =>
    if h : ∃ g : Fin n → ℝ, table g = t then priorityRowSet n M hM (Classical.choose h)
    else priorityRowSet n M hM 0
  have heq : priorityRowSet n M hM = sample ∘ table := by
    funext g
    have hex : ∃ g' : Fin n → ℝ, table g' = table g := ⟨g,rfl⟩
    simp only [sample, Function.comp_apply, dif_pos hex]
    apply Subtype.ext
    change priorityRows n M g = priorityRows n M (Classical.choose hex)
    unfold priorityRows
    rw [show (fun i j => decide ((Classical.choose hex) i ≤ (Classical.choose hex) j)) =
        (fun i j => decide (g i ≤ g j)) from Classical.choose_spec hex]
  rw [heq]
  exact (measurable_of_countable sample).comp ht

theorem gaussian_priorities_pair_ne (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ g ∂gaussianVector n, g i ≠ g j := by
  let v : Fin n → ℝ := Pi.single i 1-Pi.single j 1
  have hv : (1 : ℝ)^2 ≤ ∑ a, (v a)^2 := by
    have hi : v i = 1 := by simp [v, Pi.single_apply, hij, Ne.symm hij]
    have hb := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => sq_nonneg (v a))
      (Finset.mem_univ i)
    simpa only [hi] using hb
  have hz := gaussianVector_projection_small_ball_of_lower n v 1 0 (by norm_num) (by norm_num) hv
  have hzero : gaussianVector n {g | |∑ a, g a*v a| ≤ 0} = 0 := le_antisymm (by simpa using hz) bot_le
  rw [ae_iff]
  apply measure_mono_null _ hzero
  intro g hg
  change ¬g i ≠ g j at hg
  have he : g i = g j := not_not.mp hg
  change |∑ a, g a*v a| ≤ 0
  simp [v, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, he]

theorem gaussian_priorities_injective (n : ℕ) :
    ∀ᵐ g ∂gaussianVector n, Function.Injective g := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · filter_upwards [gaussian_priorities_pair_ne n i j hij] with g hg
    intro he
    exact False.elim (hg he)

def priorityChamber {n : ℕ} (s : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {g | ∀ i ∈ s, ∀ j, j ∉ s → g i < g j}

theorem priorityChamber_measurable {n : ℕ} (s : Finset (Fin n)) :
    MeasurableSet (priorityChamber s) := by
  unfold priorityChamber
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

theorem gaussianVector_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun g : Fin n → ℝ => fun i => g (σ i)) (gaussianVector n) (gaussianVector n) := by
  have heq : (fun g : Fin n → ℝ => fun i => g (σ i)) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm := by
    funext g i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [heq]
  exact measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) σ.symm

theorem priorityChamber_probability_eq {n : ℕ} (s t : Finset (Fin n)) (hst : s.card = t.card) :
    gaussianVector n (priorityChamber s) = gaussianVector n (priorityChamber t) := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hmem (i : Fin n) : i ∈ s ↔ σ i ∈ t := by rw [← hσ]; simp
  have hpre : (fun g : Fin n → ℝ => fun i => g (σ i)) ⁻¹' priorityChamber s = priorityChamber t := by
    ext g
    constructor
    · intro h i hi j hj
      have hi' : σ.symm i ∈ s := (hmem _).mpr (by simpa using hi)
      have hj' : σ.symm j ∉ s := fun hh => hj (by simpa using (hmem _).mp hh)
      simpa using h (σ.symm i) hi' (σ.symm j) hj'
    · intro h i hi j hj
      have hi' := (hmem i).mp hi
      have hj' : σ j ∉ t := fun hh => hj ((hmem j).mpr hh)
      exact h (σ i) hi' (σ j) hj'
  have hp := (gaussianVector_permutation n σ).measure_preimage
    (priorityChamber_measurable s).nullMeasurableSet
  rw [hpre] at hp
  exact hp.symm

theorem priorityRows_chamber (n M : ℕ) (g : Fin n → ℝ) (hg : Function.Injective g) :
    g ∈ priorityChamber (priorityRows n M g) := by
  let l := (List.finRange n).mergeSort (fun i j => decide (g i ≤ g j))
  have hs : List.Pairwise (fun i j => g i ≤ g j) l := by
    have hh := List.pairwise_mergeSort (le := fun i j : Fin n => decide (g i ≤ g j))
      (by
        intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (List.finRange n)
    simpa only [decide_eq_true_eq] using hh
  have hcross : ∀ i ∈ l.take M, ∀ j ∈ l.drop M, g i ≤ g j :=
    (List.pairwise_append.mp (by rw [List.take_append_drop]; exact hs)).2.2
  intro i hi j hj
  have hit : i ∈ l.take M := by simpa only [priorityRows, List.mem_toFinset] using hi
  have hjn : j ∉ l.take M := by simpa only [priorityRows, List.mem_toFinset] using hj
  have hjl : j ∈ l := (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_finRange j)
  have hjd : j ∈ l.drop M := by
    have hsplit : j ∈ l.take M ∨ j ∈ l.drop M := by
      rw [← List.mem_append, List.take_append_drop]
      exact hjl
    exact hsplit.resolve_left hjn
  apply lt_of_le_of_ne (hcross i hit j hjd)
  intro heq
  exact hjn (hg heq ▸ hit)

theorem priorityChambers_unique {n : ℕ} (s t : Finset (Fin n)) (hst : s.card = t.card)
    (g : Fin n → ℝ) (hs : g ∈ priorityChamber s) (ht : g ∈ priorityChamber t) : s = t := by
  classical
  apply Finset.eq_of_subset_of_card_le _ hst.ge
  intro i hi
  by_contra hit
  have hnot : ¬t ⊆ s := by
    intro hsub
    have heq : t = s := Finset.eq_of_subset_of_card_le hsub hst.le
    exact hit (heq.symm ▸ hi)
  obtain ⟨j,hjt,hjs⟩ := Finset.not_subset.mp hnot
  exact (lt_asymm (hs i hi j hjs)) (ht j hjt i hit)

theorem priorityRowSet_fiber_ae_chamber (n M : ℕ) (hM : M ≤ n) (s : PriorityRowSet n M) :
    {g | priorityRowSet n M hM g = s} =ᵐ[gaussianVector n] priorityChamber s.val := by
  filter_upwards [gaussian_priorities_injective n] with g hg
  have hch := priorityRows_chamber n M g hg
  apply propext
  constructor
  · intro hs
    change priorityRowSet n M hM g = s at hs
    have heq : priorityRows n M g = s.val := congrArg Subtype.val hs
    rwa [heq] at hch
  · intro hs
    apply Subtype.ext
    exact priorityChambers_unique _ _ ((priorityRows_card n M hM g).trans s.property.symm) g hch hs

/-- The exact mass of every fixed-size subset, for the literal merge-sort
priority sampler. Ties have Gaussian probability zero. -/
theorem gaussian_priority_singleton_probability (n M : ℕ) (hM : M ≤ n) (s : PriorityRowSet n M) :
    (gaussianVector n).real {g | priorityRowSet n M hM g = s} =
      (Fintype.card (PriorityRowSet n M) : ℝ)⁻¹ := by
  classical
  letI : Nonempty (PriorityRowSet n M) := priorityRowSet_nonempty n M hM
  let sample := priorityRowSet n M hM
  have hm : Measurable sample := priorityRowSet_measurable n M hM
  have heq (t : PriorityRowSet n M) :
      (gaussianVector n).real {g | sample g = t} = (gaussianVector n).real {g | sample g = s} := by
    calc
      _ = (gaussianVector n).real (priorityChamber t.val) :=
        measureReal_congr (priorityRowSet_fiber_ae_chamber n M hM t)
      _ = (gaussianVector n).real (priorityChamber s.val) := by
        rw [measureReal_def, measureReal_def,
          priorityChamber_probability_eq t.val s.val (t.property.trans s.property.symm)]
      _ = _ := (measureReal_congr (priorityRowSet_fiber_ae_chamber n M hM s)).symm
  have hsum : (∑ t : PriorityRowSet n M, (gaussianVector n).real {g | sample g = t}) = 1 := by
    have h := sum_measureReal_preimage_singleton (μ := gaussianVector n)
      (f := sample) Finset.univ (fun t _ => hm (measurableSet_singleton t))
    simpa only [Set.preimage, Set.mem_singleton_iff, Finset.coe_univ, Set.mem_univ,
      Set.setOf_true, probReal_univ] using h
  have hprod : (Fintype.card (PriorityRowSet n M) : ℝ)*
      (gaussianVector n).real {g | sample g = s} = 1 := by
    simpa only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  have hc : (Fintype.card (PriorityRowSet n M) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    _ = 1/(Fintype.card (PriorityRowSet n M) : ℝ) := by
      apply (eq_div_iff hc).mpr
      simpa only [mul_comm] using hprod
    _ = _ := one_div _

theorem gaussian_priority_event_probability (n M : ℕ) (hM : M ≤ n)
    (E : Set (PriorityRowSet n M)) [DecidablePred (fun s => s ∈ E)] :
    (gaussianVector n).real (priorityRowSet n M hM ⁻¹' E) =
      (Finset.univ.filter (fun s : PriorityRowSet n M => s ∈ E)).card /
        (Fintype.card (PriorityRowSet n M) : ℝ) := by
  classical
  let F := Finset.univ.filter (fun s : PriorityRowSet n M => s ∈ E)
  have hF : (F : Set (PriorityRowSet n M)) = E := by ext s; simp [F]
  have hsum := sum_measureReal_preimage_singleton (μ := gaussianVector n)
    (f := priorityRowSet n M hM) F
    (fun s _ => priorityRowSet_measurable n M hM (measurableSet_singleton s))
  rw [hF] at hsum
  have hs (s : PriorityRowSet n M) :
      (gaussianVector n).real (priorityRowSet n M hM ⁻¹' {s}) =
        (Fintype.card (PriorityRowSet n M) : ℝ)⁻¹ :=
    gaussian_priority_singleton_probability n M hM s
  simp_rw [hs] at hsum
  simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hsum.symm

end
end HierarchicalAbsoluteSpectral
