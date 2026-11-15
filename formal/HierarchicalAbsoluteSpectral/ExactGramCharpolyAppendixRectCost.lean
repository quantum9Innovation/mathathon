import HierarchicalAbsoluteSpectral.BaseKernelCosts

/-! The original comparator uses the same feasible, symmetric matrix
product costs as the main construction. Every envelope is a finite maximum
of costs of actual circuits, including padded subshapes. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

theorem exactGramAppendix_productCost_permutations
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c x y z : ℕ) (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c) :
    (kernels x y z).cost ≤ matrixProductCost kernels a b c ∧
    (kernels x z y).cost ≤ matrixProductCost kernels a b c ∧
    (kernels y x z).cost ≤ matrixProductCost kernels a b c ∧
    (kernels y z x).cost ≤ matrixProductCost kernels a b c ∧
    (kernels z x y).cost ≤ matrixProductCost kernels a b c ∧
    (kernels z y x).cost ≤ matrixProductCost kernels a b c := by
  have h1 := kernel_cost_le_rectangular kernels x y z a b c hx hy hz
  have h2 := kernel_cost_le_rectangular kernels x z y a c b hx hz hy
  have h3 := kernel_cost_le_rectangular kernels y x z b a c hy hx hz
  have h4 := kernel_cost_le_rectangular kernels y z x b c a hy hz hx
  have h5 := kernel_cost_le_rectangular kernels z x y c a b hz hx hy
  have h6 := kernel_cost_le_rectangular kernels z y x c b a hz hy hx
  unfold matrixProductCost symmetricKernelCost
  omega

structure ExactGramAppendixPhysicalBudget
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p r : ℕ) (leftCost rightCost outputCost : ℝ) : Prop where
  forward : ∀ w : ℕ, w ≤ r → ((kernels n m w).cost:ℝ) ≤ leftCost
  gram : ∀ w : ℕ, w ≤ r → w ≤ m → ((kernels w n w).cost:ℝ) ≤ leftCost
  basis : ∀ w v : ℕ, w ≤ r → w ≤ m → v ≤ w → ((kernels n w v).cost:ℝ) ≤ leftCost
  left : ∀ v : ℕ, v ≤ r → ((kernels v n m).cost:ℝ) ≤ leftCost
  right : ∀ v : ℕ, v ≤ r → ((kernels v m p).cost:ℝ) ≤ rightCost
  output : ∀ v : ℕ, v ≤ r → ((kernels n v p).cost:ℝ) ≤ outputCost

theorem exactGramAppendixPhysicalBudget_actual
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p r : ℕ) :
    ExactGramAppendixPhysicalBudget kernels n m p r
      (matrixProductCost kernels n m r:ℝ) (matrixProductCost kernels p m r:ℝ)
      (matrixProductCost kernels n r p:ℝ) := by
  constructor
  · intro w hw
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels n m r n m w le_rfl le_rfl hw).1
  · intro w hwr hwm
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels n m r n w w le_rfl hwm hwr).2.2.1
  · intro w v hwr hwm hv
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels n m r n w v le_rfl hwm (hv.trans hwr)).1
  · intro v hv
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels n m r n m v le_rfl le_rfl hv).2.2.2.2.1
  · intro v hv
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels p m r p m v le_rfl le_rfl hv).2.2.2.2.2
  · intro v hv
    exact_mod_cast (exactGramAppendix_productCost_permutations kernels n r p n v p le_rfl hv le_rfl).1

end
end HierarchicalAbsoluteSpectral
