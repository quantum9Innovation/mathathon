import HierarchicalAbsoluteSpectral.BaseMainRandomizedCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

def rectangularKernelCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin (a+1) => Finset.univ.sup (fun j : Fin (b+1) =>
    Finset.univ.sup (fun k : Fin (c+1) => (K i.val j.val k.val).cost)))

theorem kernel_cost_le_rectangular (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c A B C : ℕ) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    (K a b c).cost ≤ rectangularKernelCost K A B C := by
  apply (Finset.le_sup (f := fun k : Fin (C+1) => (K a b k.val).cost)
    (Finset.mem_univ (⟨c,by omega⟩ : Fin (C+1)))).trans
  apply (Finset.le_sup (f := fun j : Fin (B+1) =>
    Finset.univ.sup (fun k : Fin (C+1) => (K a j.val k.val).cost))
      (Finset.mem_univ (⟨b,by omega⟩ : Fin (B+1)))).trans
  exact Finset.le_sup (f := fun i : Fin (A+1) => Finset.univ.sup (fun j : Fin (B+1) =>
    Finset.univ.sup (fun k : Fin (C+1) => (K i.val j.val k.val).cost)))
      (Finset.mem_univ (⟨a,by omega⟩ : Fin (A+1)))

theorem rectangularKernelCost_mono (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    rectangularKernelCost K a b c ≤ rectangularKernelCost K A B C := by
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro j _
  apply Finset.sup_le
  intro k _
  exact kernel_cost_le_rectangular K _ _ _ A B C (by omega) (by omega) (by omega)

/-- A feasible matrix-product cost envelope, monotone in dimensions and
symmetric in all tensor legs. Every term is the cost of an actual circuit. -/
def symmetricKernelCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) : ℕ :=
  max (rectangularKernelCost K a b c) (max (rectangularKernelCost K a c b)
    (max (rectangularKernelCost K b a c) (max (rectangularKernelCost K b c a)
      (max (rectangularKernelCost K c a b) (rectangularKernelCost K c b a)))))

theorem symmetricKernelCost_swap (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    symmetricKernelCost K a b c=symmetricKernelCost K b a c := by
  unfold symmetricKernelCost
  omega

theorem symmetricKernelCost_rotate (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    symmetricKernelCost K a b c=symmetricKernelCost K c a b := by
  unfold symmetricKernelCost
  omega

theorem symmetricKernelCost_mono (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    symmetricKernelCost K a b c ≤ symmetricKernelCost K A B C := by
  have h1 := rectangularKernelCost_mono K ha hb hc
  have h2 := rectangularKernelCost_mono K ha hc hb
  have h3 := rectangularKernelCost_mono K hb ha hc
  have h4 := rectangularKernelCost_mono K hb hc ha
  have h5 := rectangularKernelCost_mono K hc ha hb
  have h6 := rectangularKernelCost_mono K hc hb ha
  unfold symmetricKernelCost
  omega

theorem kernel_cost_le_symmetric (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c A B C : ℕ) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    (K a b c).cost ≤ symmetricKernelCost K A B C :=
  (kernel_cost_le_rectangular K a b c A B C ha hb hc).trans (le_max_left _ _)

theorem symmetricKernelCost_bound (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 0 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (a b c N : ℕ) (hN : 1 ≤ N) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    (symmetricKernelCost K a b c:ℝ) ≤ (Ck+1)*(N:ℝ)^p0 := by
  have hrect (a b c : ℕ) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
      rectangularKernelCost K a b c ≤ ⌈Ck*(N:ℝ)^p0⌉₊ := by
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    apply Finset.sup_le
    intro k _
    exact_mod_cast (hK i.val j.val k.val N hN (by omega) (by omega) (by omega)).trans
      (Nat.le_ceil (Ck*(N:ℝ)^p0))
  have hmax : symmetricKernelCost K a b c ≤ ⌈Ck*(N:ℝ)^p0⌉₊ := by
    have h1 := hrect a b c ha hb hc
    have h2 := hrect a c b ha hc hb
    have h3 := hrect b a c hb ha hc
    have h4 := hrect b c a hb hc ha
    have h5 := hrect c a b hc ha hb
    have h6 := hrect c b a hc hb ha
    unfold symmetricKernelCost
    omega
  have hceil : (⌈Ck*(N:ℝ)^p0⌉₊:ℝ) ≤ Ck*(N:ℝ)^p0+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0≤Ck*(N:ℝ)^p0)).le
  have hpow : 1 ≤ (N:ℝ)^p0 := Real.one_le_rpow (by exact_mod_cast hN) hp
  exact (Nat.cast_le.mpr hmax).trans (hceil.trans (by nlinarith))

def matrixProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) : ℕ :=
  symmetricKernelCost K a b c+a*b+b*c+c*a+1

theorem matrixProductCost_swap (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    matrixProductCost K a b c=matrixProductCost K b a c := by
  unfold matrixProductCost
  rw [symmetricKernelCost_swap K a b c]
  ring

theorem matrixProductCost_rotate (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    matrixProductCost K a b c=matrixProductCost K c a b := by
  unfold matrixProductCost
  rw [symmetricKernelCost_rotate K a b c]
  ring

theorem matrixProductCost_mono (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    matrixProductCost K a b c ≤ matrixProductCost K A B C := by
  have h0 := symmetricKernelCost_mono K ha hb hc
  have h1 := Nat.mul_le_mul ha hb
  have h2 := Nat.mul_le_mul hb hc
  have h3 := Nat.mul_le_mul hc ha
  unfold matrixProductCost
  omega

theorem kernel_cost_le_matrixProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c A B C : ℕ) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    (K a b c).cost ≤ matrixProductCost K A B C := by
  have hh := kernel_cost_le_symmetric K a b c A B C ha hb hc
  unfold matrixProductCost
  omega

theorem matrixProductCost_scalar_floor (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c : ℕ) : b*c+1 ≤ matrixProductCost K a b c := by
  unfold matrixProductCost
  omega

theorem matrixProductCost_core_bound (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (a b c N : ℕ) (hN : 1 ≤ N) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    (matrixProductCost K a b c:ℝ) ≤ (Ck+5)*(N:ℝ)^p0 := by
  have hs := symmetricKernelCost_bound K Ck p0 hC (by linarith) hK a b c N hN ha hb hc
  have hvol : a*b+b*c+c*a ≤ 3*N*N := by
    have h1 := Nat.mul_le_mul ha hb
    have h2 := Nat.mul_le_mul hb hc
    have h3 := Nat.mul_le_mul hc ha
    nlinarith
  have hvol' : (a:ℝ)*b+(b:ℝ)*c+(c:ℝ)*a ≤ 3*(N:ℝ)*(N:ℝ) := by exact_mod_cast hvol
  have hnR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp0 : 0 ≤ p0 := by linarith
  have hsq : (N:ℝ)^2 ≤ (N:ℝ)^p0 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hnR hp
  have hpow : 1 ≤ (N:ℝ)^p0 := Real.one_le_rpow hnR hp0
  unfold matrixProductCost
  push_cast
  nlinarith

end
end HierarchicalAbsoluteSpectral
