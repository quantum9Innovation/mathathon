import HierarchicalAbsoluteSpectral.BaseKernelCosts
import HierarchicalAbsoluteSpectral.BaseMainStrongCost
import HierarchicalAbsoluteSpectral.BaseFixedRangeCost

/-! Numeric physical-range and explicit-output costs. Rectangular product
costs retain the original input/output dimensions; only the small PSD
factorization is bounded by a core power. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p k r w L : ℕ}

def fixedOutputInputCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p r : ℕ) : ℕ :=
  matrixProductCost K n m (r+1)+matrixProductCost K p m (r+1)

def fixedOutputCoreCost (Ck p0 : ℝ) (m : ℕ) : ℝ :=
  (Ck+1)*(m:ℝ)^p0

theorem fixedOutputInputCost_ge_one
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) :
    1 ≤ fixedOutputInputCost K n m p r := by
  have hh := matrixProductCost_scalar_floor K n m (r+1)
  dsimp [fixedOutputInputCost]
  omega

theorem fixedOutputInputCost_block_floor
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) :
    m*(r+1)+1 ≤ fixedOutputInputCost K n m p r := by
  have hh := matrixProductCost_scalar_floor K n m (r+1)
  dsimp [fixedOutputInputCost]
  omega

theorem kernel_cost_le_matrixProductCost_cyclic
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    (K a b c).cost ≤ matrixProductCost K b c a := by
  have hh := kernel_cost_le_matrixProductCost K a b c a b c le_rfl le_rfl le_rfl
  rw [← matrixProductCost_rotate K b c a] at hh
  exact hh

theorem kernelColumnWorkCap_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m r w : ℕ)
    (hwm : w ≤ m) (hwr : w ≤ r) :
    kernelColumnWorkCap K n w w ≤ matrixProductCost K n m (r+1) := by
  apply Finset.sup_le
  intro d _
  exact kernel_cost_le_matrixProductCost K n w d.val n m (r+1)
    le_rfl hwm (by omega)

theorem projectionOutputWorkCap_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) :
    projectionOutputWorkCap K n m p r ≤
      fixedOutputInputCost K n m p r+matrixProductCost K n r p := by
  apply Finset.sup_le
  intro w _
  have h1 := kernel_cost_le_matrixProductCost_cyclic K w.val n m
  have h1' := matrixProductCost_mono K (a:=n) (b:=m) (c:=w.val)
    (A:=n) (B:=m) (C:=r+1) le_rfl le_rfl (by omega)
  have h2 := kernel_cost_le_matrixProductCost K w.val m p (r+1) m p (by omega) le_rfl le_rfl
  have h2eq : matrixProductCost K (r+1) m p = matrixProductCost K p m (r+1) := by
    rw [← matrixProductCost_rotate K m p (r+1), matrixProductCost_swap K m p (r+1)]
  rw [h2eq] at h2
  have h3 := kernel_cost_le_matrixProductCost K n w.val p n r p le_rfl (by omega) le_rfl
  dsimp [fixedOutputInputCost]
  omega

theorem psdGramCost_fixed_output_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (m w : ℕ) (hwm : w ≤ m) :
    (psdGramCost K w:ℝ) ≤ 9*fixedOutputCoreCost Ck p0 m := by
  by_cases hw : 1 ≤ w
  · have hK' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
        a ≤ N → b ≤ N → c ≤ N → ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0 :=
      fun a b c N _ hN ha hb hc => hK a b c N hN ha hb hc
    have hh := psdGramCost_bound K Ck p0 hC hp hK' w hw
    have hpow : (w:ℝ)^p0 ≤ (m:ℝ)^p0 :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hwm) (by linarith)
    calc
      _ ≤ 9*(Ck+1)*(w:ℝ)^p0 := hh
      _ ≤ 9*(Ck+1)*(m:ℝ)^p0 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by dsimp [fixedOutputCoreCost]; ring
  · have hw0 : w=0 := by omega
    rw [hw0,psdGramCost]
    dsimp [fixedOutputCoreCost]
    norm_num only [Nat.cast_zero]
    positivity

theorem exactRangeWorkCap_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (n m r w : ℕ) (hrm : r ≤ m) (hwr : w ≤ r) :
    (exactRangeWorkCap K n w:ℝ) ≤
      2*(matrixProductCost K n m (r+1):ℝ)+9*fixedOutputCoreCost Ck p0 m := by
  have h1 := (kernel_cost_le_matrixProductCost_cyclic K w n w).trans
    (matrixProductCost_mono K (a:=n) (b:=w) (c:=w)
      (A:=n) (B:=m) (C:=r+1) le_rfl (hwr.trans hrm) (by omega))
  have h2 := kernelColumnWorkCap_product_bound K n m r w (hwr.trans hrm) hwr
  have h3 := psdGramCost_fixed_output_bound K Ck p0 hC hp hK m w (hwr.trans hrm)
  have h1R : ((K w n w).cost:ℝ) ≤ matrixProductCost K n m (r+1) := by exact_mod_cast h1
  have h2R : (kernelColumnWorkCap K n w w:ℝ) ≤ matrixProductCost K n m (r+1) := by exact_mod_cast h2
  unfold exactRangeWorkCap
  push_cast
  linarith

theorem physicalRangeProgram_work_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hrm : r ≤ m) (hwr : w ≤ r) :
    ((physicalRangeProgram K PZ U).work:ℝ) ≤
      (PZ.cost:ℝ)+2*(matrixProductCost K n m (r+1):ℝ)+9*fixedOutputCoreCost Ck p0 m := by
  have hh : ((physicalRangeProgram K PZ U).work:ℝ) ≤
      (PZ.cost:ℝ)+(exactRangeWorkCap K n w:ℝ) := by
    exact_mod_cast physicalRangeProgram_work_bound K PZ U
  have hr := exactRangeWorkCap_product_bound K Ck p0 hC hp hK n m r w hrm hwr
  push_cast at hh
  linarith

theorem exactPhysicalOutputProgram_work_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {Z : Matrix (Fin n) (Fin k) ℝ} (PZ : MatrixAction Z w)
    (U : Matrix (Fin k) (Fin w) ℝ) (hw : w ≤ r) (hrm : r ≤ m) :
    ((exactPhysicalOutputProgram K A B PZ U hw).work:ℝ) ≤
      (PZ.cost:ℝ)+3*(fixedOutputInputCost K n m p r:ℝ)+
        (matrixProductCost K n r p:ℝ)+9*fixedOutputCoreCost Ck p0 m := by
  have hh : ((exactPhysicalOutputProgram K A B PZ U hw).work:ℝ) ≤
      (PZ.cost:ℝ)+(exactRangeWorkCap K n w:ℝ)+(projectionOutputWorkCap K n m p r:ℝ) := by
    exact_mod_cast exactPhysicalOutputProgram_work_bound K A B PZ U hw
  have hr := exactRangeWorkCap_product_bound K Ck p0 hC hp hK n m r w hrm hw
  have ho : (projectionOutputWorkCap K n m p r:ℝ) ≤
      (fixedOutputInputCost K n m p r:ℝ)+(matrixProductCost K n r p:ℝ) := by
    exact_mod_cast projectionOutputWorkCap_product_bound K n m p r
  have hA : (matrixProductCost K n m (r+1):ℝ) ≤ fixedOutputInputCost K n m p r := by
    exact_mod_cast (show matrixProductCost K n m (r+1) ≤ fixedOutputInputCost K n m p r from by
      dsimp [fixedOutputInputCost]; omega)
  linarith

theorem mainExactOutputWorkCap_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    (mainExactOutputWorkCap K I S C:ℝ) ≤
      5*(fixedOutputInputCost K n m p r:ℝ)+(matrixProductCost K n r p:ℝ)+
        9*fixedOutputCoreCost Ck p0 m := by
  let f := fun w : Fin (r+1) =>
    (K n m w.val).cost+(K m C.pair.dimension w.val).cost+
      exactRangeWorkCap K n w.val+projectionOutputWorkCap K n m p r
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (r+1)))
    Finset.univ_nonempty f
  change ((Finset.univ.sup f:ℕ):ℝ) ≤ _
  rw [hw]
  have h1 := kernel_cost_le_matrixProductCost K n m w.val n m (r+1) le_rfl le_rfl (by omega)
  have h2 := kernel_cost_le_matrixProductCost K m C.pair.dimension w.val n m (r+1)
    I.core_le_rows C.pair.dimension_le_fin (by omega)
  have h3 := exactRangeWorkCap_product_bound K Ck p0 hC hp hK n m r w.val I.rank_le_core (by omega)
  have h4 : (projectionOutputWorkCap K n m p r:ℝ) ≤
      (fixedOutputInputCost K n m p r:ℝ)+(matrixProductCost K n r p:ℝ) := by
    exact_mod_cast projectionOutputWorkCap_product_bound K n m p r
  have hA : (matrixProductCost K n m (r+1):ℝ) ≤ fixedOutputInputCost K n m p r := by
    exact_mod_cast (show matrixProductCost K n m (r+1) ≤ fixedOutputInputCost K n m p r from by
      dsimp [fixedOutputInputCost]; omega)
  have h1R : ((K n m w.val).cost:ℝ) ≤ matrixProductCost K n m (r+1) := by exact_mod_cast h1
  have h2R : ((K m C.pair.dimension w.val).cost:ℝ) ≤ matrixProductCost K n m (r+1) := by exact_mod_cast h2
  dsimp [f]
  push_cast
  linarith

end
end HierarchicalAbsoluteSpectral
