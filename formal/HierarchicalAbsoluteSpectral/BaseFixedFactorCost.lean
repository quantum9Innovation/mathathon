import HierarchicalAbsoluteSpectral.BaseFixedLeafCost
import HierarchicalAbsoluteSpectral.BaseFixedDegreeCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

def fixedFineLog (I : FixedProblem n m p r L) : ℝ :=
  1+∑ j : Fin L, mainFineNeumannLog I j.val

theorem fixedFineLog_ge_one (I : FixedProblem n m p r L) : 1 ≤ fixedFineLog I := by
  have hs : 0 ≤ ∑ j : Fin L, mainFineNeumannLog I j.val :=
    Finset.sum_nonneg (fun j _ => le_trans (by norm_num) (mainFineNeumannLog_ge_one I j.val))
  dsimp [fixedFineLog]
  linarith

theorem fixedFineLog_level_le (I : FixedProblem n m p r L) (j : ℕ) (hj : j<L) :
    mainFineNeumannLog I j ≤ fixedFineLog I := by
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin L)))
    (f := fun j : Fin L => mainFineNeumannLog I j.val)
    (fun j _ => le_trans (by norm_num) (mainFineNeumannLog_ge_one I j.val))
    (Finset.mem_univ (⟨j,hj⟩ : Fin L))
  dsimp [fixedFineLog]
  linarith

def fixedFineProductSum (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L, I.accuracy j*(mainFineProductCost K S j b:ℝ)

theorem mainFineProductCost_scalar_floor
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches n m p L) (k j b : ℕ) (hk : k ≤ m) :
    k*b+1 ≤ mainFineProductCost K S j b := by
  have hh := matrixProductCost_scalar_floor K (S.levelA (safeSketchIndex L (j+1))).1 m b
  have hmul := Nat.mul_le_mul_right b hk
  dsimp [mainFineProductCost]
  omega

theorem mainFactorActionCost_fine_sum
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ)
    (hA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    I.accuracy L*(mainFactorActionCost K I S C b L:ℝ) ≤
      42*fixedFineLog I*(fixedRefinementCostMultiplier I)^L*fixedFineProductSum K I S b := by
  let J := fun j => (mainFineProductCost K S j b:ℝ)
  let ell := fixedFineLog I
  have hell : 1 ≤ ell := fixedFineLog_ge_one I
  have hJ : ∀ j, 0 ≤ J j := fun j => Nat.cast_nonneg _
  have hSum : 0 ≤ fixedFineProductSum K I S b := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le (hJ j)
  have hcost0 : (K C.pair.dimension C.pair.dimension b).cost ≤ mainFineProductCost K S 0 b := by
    have hh := kernel_cost_le_matrixProductCost K C.pair.dimension C.pair.dimension b
      (S.levelA (safeSketchIndex L (0+1))).1 m b
      (C.pair.dimension_le_fin.trans (hA 0 I.depth_positive)) C.pair.dimension_le_fin le_rfl
    simp only [Nat.zero_add] at hh
    dsimp [mainFineProductCost]
    omega
  have hbase : I.accuracy 0*(K C.pair.dimension C.pair.dimension b).cost ≤ fixedFineProductSum K I S b := by
    have hh : I.accuracy 0*(K C.pair.dimension C.pair.dimension b).cost ≤ I.accuracy 0*J 0 :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcost0) (I.accuracy_positive 0 (by omega)).le
    apply hh.trans
    exact Finset.single_le_sum
      (fun j hj => mul_nonneg (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le (hJ j))
      (Finset.mem_range.mpr I.depth_positive)
  have hfine (j : ℕ) (hj : j<L) :
      (mainFineActionCost K I S C j b:ℝ)+(C.pair.dimension:ℝ)*b+1 ≤ 41*ell*J j := by
    have hf := mainFineActionCost_product_bound K I S C j b (hA j hj) (hB j hj)
    have hl := fixedFineLog_level_le I j hj
    have hscalar : (C.pair.dimension:ℝ)*b+1 ≤ J j := by
      dsimp only [J]
      exact_mod_cast mainFineProductCost_scalar_floor K S C.pair.dimension j b C.pair.dimension_le_fin
    have hm := mul_le_mul_of_nonneg_right hl (show 0≤40*J j by positivity)
    have hm' := mul_le_mul_of_nonneg_right hell (hJ j)
    change _ ≤ 41*ell*J j
    nlinarith
  have hsum : (∑ j ∈ Finset.range L, I.accuracy j*
      ((mainFineActionCost K I S C j b:ℝ)+(C.pair.dimension:ℝ)*b+1)) ≤
        41*ell*fixedFineProductSum K I S b := by
    calc
      _ ≤ ∑ j ∈ Finset.range L, I.accuracy j*(41*ell*J j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hfine j (Finset.mem_range.mp hj))
          (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le
      _ = _ := by
        dsimp [fixedFineProductSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [J]
        ring
  have hinside : I.accuracy 0*(K C.pair.dimension C.pair.dimension b).cost+
      (∑ j ∈ Finset.range L, I.accuracy j*
        ((mainFineActionCost K I S C j b:ℝ)+(C.pair.dimension:ℝ)*b+1)) ≤
          42*ell*fixedFineProductSum K I S b := by
    have hm := mul_le_mul_of_nonneg_right hell hSum
    nlinarith only [hbase,hsum,hm]
  have hh := mainFactorActionCost_fixed_depth K I S C b
  have hp : 0 ≤ (fixedRefinementCostMultiplier I)^L :=
    pow_nonneg (le_trans (by norm_num) (fixedRefinementCostMultiplier_ge_one I)) _
  exact hh.trans ((mul_le_mul_of_nonneg_left hinside hp).trans_eq (by dsimp [ell]; ring))

theorem mainActualFactorActionCost_fine_sum
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I)
    (C : MainSupportData (mainSketchProgram I g).eval) (b : ℕ) :
    I.accuracy L*(mainFactorActionCost K I (mainSketchProgram I g).eval C b L:ℝ) ≤
      42*fixedFineLog I*(fixedRefinementCostMultiplier I)^L*
        fixedFineProductSum K I (mainSketchProgram I g).eval b :=
  mainFactorActionCost_fine_sum K I _ C b
    (fun j _ => mainSketchProgram_core_le_rowsA I g _) (fun j _ => mainSketchProgram_core_le_rowsB I g _)

end
end HierarchicalAbsoluteSpectral
