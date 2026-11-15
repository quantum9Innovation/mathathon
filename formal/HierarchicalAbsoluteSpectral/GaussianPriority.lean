import HierarchicalAbsoluteSpectral.GaussianLinear
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fintype

/-! Gaussian priorities implement exact uniform sampling without replacement. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def priorityRows (n M : ℕ) (g : Fin n → ℝ) : Finset (Fin n) :=
  (((List.finRange n).mergeSort (fun i j => decide (g i ≤ g j))).take M).toFinset

theorem priorityRows_card (n M : ℕ) (hM : M ≤ n) (g : Fin n → ℝ) :
    (priorityRows n M g).card = M := by
  have hn : (((List.finRange n).mergeSort (fun i j => decide (g i ≤ g j))).take M).Nodup :=
    List.Nodup.take _ ((List.nodup_mergeSort).mpr (List.nodup_finRange n))
  rw [priorityRows, List.toFinset_card_of_nodup hn, List.length_take,
    List.length_mergeSort, List.length_finRange, Nat.min_eq_left hM]

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

instance priorityRowSet_nonempty (n M : ℕ) (hM : M ≤ n) : Nonempty (PriorityRowSet n M) :=
  ⟨priorityRowSet n M hM 0⟩

theorem priorityRowSet_measurable (n M : ℕ) (hM : M ≤ n) :
    Measurable (priorityRowSet n M hM) := by
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
    unfold priorityRowSet priorityRows
    rw [show (fun i j => decide ((Classical.choose hex) i ≤ (Classical.choose hex) j)) =
        (fun i j => decide (g i ≤ g j)) from Classical.choose_spec hex]
  rw [heq]
  exact (measurable_of_countable sample).comp ht

theorem gaussian_priorities_pair_ne (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ g ∂gaussianVector n, g i ≠ g j := by
  let v : Fin n → ℝ := Pi.single i 1-Pi.single j 1
  have hv : (1 : ℝ)^2 ≤ ∑ a, (v a)^2 := by
    have heq : (∑ a, (v a)^2) = 2 := by
      unfold v
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero, one_pow]
      have : ∑ a ∈ Finset.univ \ {i}, (Pi.single i (1 : ℝ) a-Pi.single j 1 a)^2 = 1 := by
        rw [Finset.sum_eq_single j]
        · simp [hij, Ne.symm hij]
        · intro a ha haj
          have hai : a ≠ i := by simpa using (Finset.mem_sdiff.mp ha).2
          simp [Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj]
        · simp [hij, Ne.symm hij]
      rw [this]
      norm_num
    rw [heq]
    norm_num
  have hz := gaussianVector_projection_small_ball_of_lower n v 1 0 (by norm_num) (by norm_num) hv
  have hzero : gaussianVector n {g | |∑ a, g a*v a| ≤ 0} = 0 := le_antisymm (by simpa using hz) bot_le
  rw [ae_iff]
  apply measure_mono_null _ hzero
  intro g hg
  change ¬g i ≠ g j at hg
  have he : g i = g j := not_not.mp hg
  simp only [Set.mem_setOf_eq, v, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_mul_pi_single, he, sub_self, abs_zero, le_refl]

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
  exact MeasurableSet.forall (fun i => MeasurableSet.forall (fun _ =>
    MeasurableSet.forall (fun j => MeasurableSet.forall (fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)))))

end
end HierarchicalAbsoluteSpectral
