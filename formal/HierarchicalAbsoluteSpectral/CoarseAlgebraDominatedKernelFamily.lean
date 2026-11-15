import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedKernelFamily
import HierarchicalAbsoluteSpectral.CoarseAlgebraDominatedWideCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Filter

theorem FixedRowKernelEnvelopes.of_cost_le {m : ℕ}
    {K P : ∀ a b c : ℕ, ArithmeticKernel a b c} {χ : ℝ}
    (hK : FixedRowKernelEnvelopes m K χ)
    (hP : ∀ a b c : ℕ, (P a b c).cost ≤ (K a b c).cost) :
    FixedRowKernelEnvelopes m P χ := by
  constructor
  · intro a b c hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.forward a b c hb hc)
  · intro a b c ha hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.adjoint a b c ha hc)
  · intro a b c ha hb
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.transpose_forward a b c ha hb)
  · intro a b c ha hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.transpose_adjoint a b c ha hc)

/-- One literal subpolynomial-overhead kernel family also retains the
classical rectangular bound, so exact wide-block range deflation satisfies
its quadratic-in-width bound for the same compiled algorithm. -/
theorem exists_fixed_classically_dominated_hierarchy_kernel_family (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℕ → ℝ) (C : ℝ),
      0 < C ∧ (∀ m, 1 ≤ χ m) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      ∀ (m : ℕ) (hm : 0 < m), FixedRowKernelEnvelopes m (K m hm) (χ m) ∧
        (∀ a b c L : ℕ, 1 ≤ L → a ≤ L → b ≤ L → c ≤ L →
          ((K m hm a b c).cost:ℝ) ≤ C*(L:ℝ)^(9/4+ζ)) ∧
        (∀ a b c : ℕ, (K m hm a b c).cost ≤ 2*a*b*c) := by
  obtain ⟨K,χ,C,hC,hχ,hSub,hK⟩ := exists_fixed_hierarchy_kernel_family ζ hζ
  refine ⟨fun m hm => classicallyDominatedKernels (K m hm),χ,C,hC,hχ,hSub,?_⟩
  intro m hm
  refine ⟨(hK m hm).1.of_cost_le (classicallyDominatedKernels_cost_le _),?_,
    classicallyDominatedKernels_cost_classical _⟩
  intro a b c D hD ha hb hc
  exact (Nat.cast_le.mpr (classicallyDominatedKernels_cost_le (K m hm) a b c)).trans
    ((hK m hm).2 a b c D hD ha hb hc)

end
end HierarchicalAbsoluteSpectral
