import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRawCost

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

theorem exactGramAppendixRectCost_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C q : ℝ)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^q)
    (a b c m : ℕ) (hm : 1 ≤ m) (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) :
    (exactGramAppendixRectCost kernels a b c : ℝ) ≤ C*(m:ℝ)^q := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin (a+1) × Fin (b+1) × Fin (c+1))) Finset.univ_nonempty
    (fun i => (kernels i.1.val i.2.1.val i.2.2.val).cost)
  change ((Finset.univ.sup (fun i : Fin (a+1) × Fin (b+1) × Fin (c+1) =>
    (kernels i.1.val i.2.1.val i.2.2.val).cost) : ℕ) : ℝ) ≤ _
  rw [hi]
  exact hK _ _ _ m hm (by have h := i.1.isLt; omega)
    (by have h := i.2.1.isLt; omega) (by have h := i.2.2.isLt; omega)

theorem exactGramAppendixRangeCoreCost_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^q)
    (r m : ℕ) (hm : 1 ≤ m) (hr : r ≤ m) :
    (exactGramAppendixRangeCoreCost kernels r : ℝ) ≤ 9*(C+1)*(m:ℝ)^q := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin (r+1))) Finset.univ_nonempty
    (fun i => psdGramCost kernels i.val)
  change ((Finset.univ.sup (fun i : Fin (r+1) => psdGramCost kernels i.val) : ℕ) : ℝ) ≤ _
  rw [hi]
  have hw : i.val ≤ m := by have hh := i.isLt; omega
  by_cases hi0 : i.val = 0
  · rw [hi0, psdGramCost]
    simp only [Nat.cast_zero]
    positivity
  · apply (psdGramCost_bound kernels C q hC hq (fun a b c N _ => hK a b c N)
      i.val (by omega)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw) (by linarith)

theorem exactGramAppendixLiftRawCost_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^q)
    (n m p k r : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) (hr : r ≤ m) :
    (exactGramAppendixLiftRawCost kernels n m p k r : ℝ) ≤ 10*(C+1)*(m:ℝ)^q+
      (exactGramAppendixRectCost kernels n m r : ℝ)+
      (exactGramAppendixRectCost kernels r n r : ℝ)+
      (exactGramAppendixRectCost kernels n r r : ℝ)+
      (exactGramAppendixRectCost kernels r n m : ℝ)+
      (exactGramAppendixRectCost kernels r m p : ℝ)+
      (exactGramAppendixRectCost kernels n r p : ℝ) := by
  have hs := exactGramAppendixRectCost_bound kernels C q hK m k r m hm le_rfl hk hr
  have hpsd := exactGramAppendixRangeCoreCost_bound kernels C q hC hq hK r m hm hr
  have hkpow : (k:ℝ) ≤ (m:ℝ)^q := by
    calc
      _ ≤ (m:ℝ) := by exact_mod_cast hk
      _ = (m:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  unfold exactGramAppendixLiftRawCost
  push_cast
  nlinarith

end
end HierarchicalAbsoluteSpectral
