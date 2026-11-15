import HierarchicalAbsoluteSpectral.BaseRefinementLogCost
import HierarchicalAbsoluteSpectral.MainOperatorCorrectness

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedRefinementLog (I : FixedProblem n m p r L) : ℝ :=
  1+∑ j : Fin L, refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
    (I.accuracy (j.val+1)) (hierarchyUpper j.val)

theorem fixedRefinementLog_level (I : FixedProblem n m p r L) (j : ℕ) (hj : j<L) :
    1 ≤ refinementLogBudget (I.accuracy (j+1)/I.accuracy j)
      (I.accuracy (j+1)) (hierarchyUpper j) := by
  have hH := I.accuracy_positive j (by omega)
  have hh := I.accuracy_positive (j+1) (by omega)
  have hη : 0 < 8*(I.accuracy (j+1)/I.accuracy j) := by positivity
  have hη1 : 8*(I.accuracy (j+1)/I.accuracy j) ≤ 1/8 := by
    have hrat := I.refinement_ratio j hj
    linarith
  have hτ : 0 < refinementTolerance (I.accuracy (j+1)) (hierarchyUpper j) := by
    dsimp [refinementTolerance]
    have hB := hierarchyUpper_nonneg j
    positivity
  have hτ1 : refinementTolerance (I.accuracy (j+1)) (hierarchyUpper j) < 1/4 := by
    have hb := I.accuracy_bounded (j+1) (by omega)
    have hB := hierarchyUpper_nonneg j
    dsimp [refinementTolerance]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<10^6*(1+hierarchyUpper j))).mpr
    nlinarith
  exact (inverseRoot_log_budget _ _ hη hη1 hτ hτ1).1

theorem fixedRefinementLog_ge_one (I : FixedProblem n m p r L) : 1 ≤ fixedRefinementLog I := by
  have hs : 0 ≤ ∑ j : Fin L, refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
      (I.accuracy (j.val+1)) (hierarchyUpper j.val) :=
    Finset.sum_nonneg (fun j _ => le_trans (by norm_num) (fixedRefinementLog_level I j.val j.isLt))
  dsimp [fixedRefinementLog]
  linarith

theorem fixedRefinementLog_level_le (I : FixedProblem n m p r L) (j : ℕ) (hj : j<L) :
    refinementLogBudget (I.accuracy (j+1)/I.accuracy j)
      (I.accuracy (j+1)) (hierarchyUpper j) ≤ fixedRefinementLog I := by
  have hs := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin L)))
    (f := fun j : Fin L => refinementLogBudget (I.accuracy (j.val+1)/I.accuracy j.val)
      (I.accuracy (j.val+1)) (hierarchyUpper j.val))
    (fun j _ => le_trans (by norm_num) (fixedRefinementLog_level I j.val j.isLt))
    (Finset.mem_univ (⟨j,hj⟩ : Fin L))
  dsimp [fixedRefinementLog]
  linarith

def fixedRefinementCostMultiplier (I : FixedProblem n m p r L) : ℝ :=
  200000000000*(fixedRefinementLog I)^2

theorem fixedRefinementCostMultiplier_ge_one (I : FixedProblem n m p r L) :
    1 ≤ fixedRefinementCostMultiplier I := by
  have hh := fixedRefinementLog_ge_one I
  dsimp [fixedRefinementCostMultiplier]
  nlinarith

theorem mainFactorActionCost_step
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (b j : ℕ) (hj : j<L) :
    (mainFactorActionCost kernels I S C b (j+1):ℝ) ≤
      fixedRefinementCostMultiplier I*(I.accuracy j/I.accuracy (j+1))*
        ((mainFactorActionCost kernels I S C b j:ℝ)+mainFineActionCost kernels I S C j b+
          (C.pair.dimension:ℝ)*b+1) := by
  let P := mainFactorActionCost kernels I S C b j
  let J := mainFineActionCost kernels I S C j b
  let ε := I.accuracy (j+1)/I.accuracy j
  let W := refinementLogBudget ε (I.accuracy (j+1)) (hierarchyUpper j)
  let A : ℝ := (P:ℝ)+(J:ℝ)+(C.pair.dimension:ℝ)*b+1
  have hH := I.accuracy_positive j (by omega)
  have hh := I.accuracy_positive (j+1) (by omega)
  have hε : 0 < ε := div_pos hh hH
  have hε1 : ε ≤ 1/1024 := I.refinement_ratio j hj
  have hb := I.accuracy_bounded (j+1) (by omega)
  have hB := hierarchyUpper_nonneg j
  have henv := refinementActionEnvelope_log_bound P P J ε (I.accuracy (j+1))
    (hierarchyUpper j) hε hε1 hh hb hB C.pair.dimension b
  have he : mainFactorActionCost kernels I S C b (j+1)=
      refinementActionEnvelope P P J ε (I.accuracy (j+1)) (hierarchyUpper j)
        hε hh hB C.pair.dimension b := by
    simp only [mainFactorActionCost,safeAccuracy_eq I j (by omega),
      safeAccuracy_eq I (j+1) (by omega),P,J,ε]
  rw [he]
  have hW : 1 ≤ W := fixedRefinementLog_level I j hj
  have hWle : W ≤ fixedRefinementLog I := fixedRefinementLog_level_le I j hj
  have hsquares : W^2 ≤ (fixedRefinementLog I)^2 := by nlinarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcount : (P:ℝ)+(P:ℝ)+(J:ℝ)+(C.pair.dimension:ℝ)*b+1 ≤ 2*A := by
    dsimp [A]
    have hJ : (0:ℝ)≤J := Nat.cast_nonneg _
    have hkb : (0:ℝ)≤(C.pair.dimension:ℝ)*b := by positivity
    linarith
  have hmul := mul_le_mul hsquares hcount
    (by positivity : (0:ℝ)≤(P:ℝ)+(P:ℝ)+(J:ℝ)+(C.pair.dimension:ℝ)*b+1)
    (by positivity : (0:ℝ)≤(fixedRefinementLog I)^2)
  have hmul' := mul_le_mul_of_nonneg_left hmul (by positivity : (0:ℝ)≤100000000000/ε)
  have hinv : 1/ε=I.accuracy j/I.accuracy (j+1) := by dsimp [ε]; field_simp
  change _ ≤ fixedRefinementCostMultiplier I*(I.accuracy j/I.accuracy (j+1))*A
  calc
    _ ≤ (100000000000/ε)*W^2*((P:ℝ)+(P:ℝ)+(J:ℝ)+(C.pair.dimension:ℝ)*b+1) := henv
    _ ≤ (100000000000/ε)*((fixedRefinementLog I)^2*(2*A)) := by nlinarith only [hmul']
    _ = _ := by dsimp [fixedRefinementCostMultiplier]; rw [div_eq_mul_one_div,hinv]; ring

/-- The actual fixed-depth factor action has the manuscript's telescoping
weights. The common overhead is an explicit power of a logarithmic budget;
it includes coefficient construction on every invocation. -/
theorem mainFactorActionCost_fixed_depth
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) :
    I.accuracy L*(mainFactorActionCost kernels I S C b L:ℝ) ≤
      (fixedRefinementCostMultiplier I)^L*
        (I.accuracy 0*(kernels C.pair.dimension C.pair.dimension b).cost+
          ∑ j ∈ Finset.range L, I.accuracy j*
            ((mainFineActionCost kernels I S C j b:ℝ)+(C.pair.dimension:ℝ)*b+1)) := by
  have hh := family_cost_recurrence_unfold (fixedRefinementCostMultiplier I) I.accuracy
    (fun j => (mainFactorActionCost kernels I S C b j:ℝ))
    (fun j => (mainFineActionCost kernels I S C j b:ℝ)+(C.pair.dimension:ℝ)*b+1) L
    (fixedRefinementCostMultiplier_ge_one I) I.accuracy_positive
    (fun j _ => by positivity)
    (fun j hj => by simpa only [add_assoc] using mainFactorActionCost_step kernels I S C b j hj)
  simpa only [mainFactorActionCost] using hh

end
end HierarchicalAbsoluteSpectral
