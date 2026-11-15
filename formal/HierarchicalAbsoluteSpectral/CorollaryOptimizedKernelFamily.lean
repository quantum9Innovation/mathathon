import HierarchicalAbsoluteSpectral.CorollaryOptimizedExponents
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedOutputKernelFamily

/-! A single verified kernel family is used by both comparator programs.
The true-Gram candidates preserve its row, core, classical and dense-output
envelopes, and cover every possible stored-sketch row count uniformly. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms Matmul.RectangularOptimization
open scoped Topology

def comparatorDimensionKernelFallback
    (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c)
    (N m : ℕ) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  if hm : 0 < m then K N m hm else classicalArithmeticKernels

def optimizedComparatorKernels
    (P : ∀ j n : ℕ, ArithmeticKernel n (width (1+dStar+1/(j+1:ℝ)) n) n)
    (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c)
    (N m : ℕ) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  comparatorGramKernelFamily (1+dStar) P (comparatorDimensionKernelFallback K N m) m

def comparatorGramShapeWorkCap (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (m N : ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin (m+1) × Fin (N+1) × Fin (m+1) =>
    (K i.1.val i.2.1.val i.2.2.val).cost)

theorem comparatorGramShapeWorkCap_le
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (m N a b c : ℕ) (ha : a ≤ m) (hb : b ≤ N) (hc : c ≤ m) :
    (K a b c).cost ≤ comparatorGramShapeWorkCap K m N :=
  Finset.le_sup (f:=fun i : Fin (m+1) × Fin (N+1) × Fin (m+1) =>
    (K i.1.val i.2.1.val i.2.2.val).cost)
    (Finset.mem_univ (⟨a,by omega⟩,⟨b,by omega⟩,⟨c,by omega⟩))

theorem exists_optimized_comparator_kernel_family (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ N m a b c : ℕ, ArithmeticKernel a b c) (χ χOut : ℕ → ℝ) (C : ℝ),
      0 < C ∧ (∀ m, 1 ≤ χ m) ∧ (∀ N, 1 ≤ χOut N) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, χOut N ≤ (N:ℝ)^ε) ∧
      (∀ (N m : ℕ), 0 < m → m ≤ N →
        FixedFamilyKernelEnvelopes ζ N m (K N m) (χ m) (χOut N) C) ∧
      ∀ (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop)
        (hN : ∀ᶠ i : ℕ in atTop, 0 < N i)
        (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
          atTop (𝓝 (1+dStar))) (ε : ℝ) (hε : 0 < ε),
        ∀ᶠ i : ℕ in atTop,
          (comparatorGramShapeWorkCap (K (N i) (m i)) (m i) (N i):ℝ) ≤
            (N i:ℝ)^(2+savingStar+ε) := by
  have hκ : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  obtain ⟨P,hP⟩ := exists_comparator_gram_kernel_family_uniform (1+dStar) hκ.le
  obtain ⟨base,χ,χOut,C,hC,hχ,hχOut,hχsub,hχOutSub,hbase⟩ := exists_fixed_family_kernel ζ hζ
  let K := optimizedComparatorKernels P base
  refine ⟨K,χ,χOut,C,hC,hχ,hχOut,hχsub,hχOutSub,?_,?_⟩
  · intro N m hm hNm
    have hh := hbase N m hm hNm
    apply hh.of_cost_le
    intro a b c
    have hle := comparatorGramKernelFamily_le_fallback (1+dStar) P
      (comparatorDimensionKernelFallback base N m) m a b c
    simpa only [K,optimizedComparatorKernels,comparatorDimensionKernelFallback,dif_pos hm] using hle
  · intro m N hm hN hgrowth ε hε
    have hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i : ℕ in atTop,
        (comparatorGramShapeWorkCap (K (N i) (m i)) (m i) (N i):ℝ) ≤
          (m i:ℝ)^(rectangularBound (1+dStar)+η) := by
      intro η hη
      filter_upwards [hP m N hm hN hgrowth (fun i => comparatorDimensionKernelFallback base (N i) (m i)) η hη]
        with i hi
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup (Finset.univ:Finset
        (Fin (m i+1) × Fin (N i+1) × Fin (m i+1))) Finset.univ_nonempty
          (fun j : Fin (m i+1) × Fin (N i+1) × Fin (m i+1) =>
            (K (N i) (m i) j.1.val j.2.1.val j.2.2.val).cost)
      unfold comparatorGramShapeWorkCap
      rw [hj]
      exact hi j.1.val j.2.1.val j.2.2.val (by omega) (by omega) (by omega)
    have hE : 0 ≤ rectangularBound (1+dStar) :=
      le_trans (by norm_num) (two_le_rectangularBound hκ.le)
    have hh := sequence_cost_exponent_in_output atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
      (fun i => (comparatorGramShapeWorkCap (K (N i) (m i)) (m i) (N i):ℝ))
      (1+dStar) (rectangularBound (1+dStar)) hκ hE
      (tendsto_natCast_atTop_atTop.comp hm) (hN.mono (fun i hi => by exact_mod_cast hi))
      hgrowth hcost ε hε
    simpa only [optimized_gram_rectangular_exponent] using hh

end
end HierarchicalAbsoluteSpectral
