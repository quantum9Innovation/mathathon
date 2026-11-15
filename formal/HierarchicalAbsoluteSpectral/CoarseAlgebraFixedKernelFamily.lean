import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedRowKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matmul.RectangularPrograms Filter

def fixedHalfForwardCandidate
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (m : ℕ) (hm : 0 < m)
    (a b c : ℕ) : ArithmeticKernel a b c :=
  if h : b ≤ m ∧ c ≤ 2*width (1/2) m then fixedHalfForwardKernel K a m b c hm h.1 h.2
  else fallback a b c

def fixedHalfAdjointCandidate
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (m : ℕ) (hm : 0 < m)
    (a b c : ℕ) : ArithmeticKernel a b c :=
  if h : a ≤ m ∧ c ≤ 2*width (1/2) m then fixedHalfAdjointKernel K b m a c hm h.1 h.2
  else fallback a b c

def fixedHalfKernelFamily
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (m : ℕ) (hm : 0 < m) :
    ∀ a b c : ℕ, ArithmeticKernel a b c := fun a b c =>
  (fallback a b c).cheaper
    ((fixedHalfForwardCandidate fallback K m hm a b c).cheaper
      ((fixedHalfAdjointCandidate fallback K m hm a b c).cheaper
        ((fixedHalfForwardCandidate fallback K m hm c b a).transpose.cheaper
          (fixedHalfAdjointCandidate fallback K m hm c b a).transpose)))

structure FixedRowKernelEnvelopes (m : ℕ)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) : Prop where
  forward : ∀ a b c : ℕ, b ≤ m → c ≤ 2*width (1/2) m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(a+m:ℕ)*(m:ℝ)
  adjoint : ∀ a b c : ℕ, a ≤ m → c ≤ 2*width (1/2) m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(b+m:ℕ)*(m:ℝ)
  transpose_forward : ∀ a b c : ℕ, a ≤ 2*width (1/2) m → b ≤ m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(c+m:ℕ)*(m:ℝ)
  transpose_adjoint : ∀ a b c : ℕ, a ≤ 2*width (1/2) m → c ≤ m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(b+m:ℕ)*(m:ℝ)

theorem fixedHalfKernelFamily_cost_le_fallback
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (m : ℕ) (hm : 0 < m) (a b c : ℕ) :
    (fixedHalfKernelFamily fallback K m hm a b c).cost ≤ (fallback a b c).cost :=
  ArithmeticKernel.cheaper_cost_le_left _ _

theorem fixedHalfKernelFamily_envelopes
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m))
    (χ : ℕ → ℝ) (hχ : ∀ m, 1 ≤ χ m)
    (hK : ∀ m : ℕ, 1 ≤ m → ((K m).cost:ℝ) ≤ (m:ℝ)^2*χ m)
    (m : ℕ) (hm : 0 < m) : FixedRowKernelEnvelopes m (fixedHalfKernelFamily fallback K m hm) (χ m) := by
  have hf (a b c : ℕ) (hb : b ≤ m) (hc : c ≤ 2*width (1/2) m) :
      ((fixedHalfForwardCandidate fallback K m hm a b c).cost:ℝ) ≤ 8*χ m*(a+m:ℕ)*(m:ℝ) := by
    simp only [fixedHalfForwardCandidate,dif_pos (And.intro hb hc)]
    exact (fixedHalf_row_kernel_bounds K χ hχ hK a m b c hm hb hc).1
  have ha (a b c : ℕ) (ha : a ≤ m) (hc : c ≤ 2*width (1/2) m) :
      ((fixedHalfAdjointCandidate fallback K m hm a b c).cost:ℝ) ≤ 8*χ m*(b+m:ℕ)*(m:ℝ) := by
    simp only [fixedHalfAdjointCandidate,dif_pos (And.intro ha hc)]
    exact (fixedHalf_row_kernel_bounds K χ hχ hK b m a c hm ha hc).2
  have hmin (a b c : ℕ) : (fixedHalfKernelFamily fallback K m hm a b c).cost =
      min (fallback a b c).cost (min (fixedHalfForwardCandidate fallback K m hm a b c).cost
        (min (fixedHalfAdjointCandidate fallback K m hm a b c).cost
          (min (fixedHalfForwardCandidate fallback K m hm c b a).cost
            (fixedHalfAdjointCandidate fallback K m hm c b a).cost))) := by
    simp [fixedHalfKernelFamily]
  constructor
  · intro a b c hb hc
    apply le_trans _ (hf a b c hb hc)
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans (min_le_left _ _)
  · intro a b c hb hc
    apply le_trans _ (ha a b c hb hc)
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · intro a b c hb hc
    apply le_trans _ (hf c b a hc hb)
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · intro a b c hb hc
    apply le_trans _ (ha c b a hc hb)
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

theorem exists_fixed_hierarchy_kernel_family (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℕ → ℝ) (C : ℝ),
      0 < C ∧ (∀ m, 1 ≤ χ m) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      ∀ (m : ℕ) (hm : 0 < m), FixedRowKernelEnvelopes m (K m hm) (χ m) ∧
        ∀ a b c L : ℕ, 1 ≤ L → a ≤ L → b ≤ L → c ≤ L →
          ((K m hm a b c).cost:ℝ) ≤ C*(L:ℝ)^(9/4+ζ) := by
  obtain ⟨fallback,C,hC,hFallback⟩ := exists_full_shape_arithmetic_kernels ζ hζ
  obtain ⟨P,χ,hχ,hP,hSub⟩ := exists_fixed_half_kernel_subpolynomial
  refine ⟨fixedHalfKernelFamily fallback P,χ,C,hC,hχ,hSub,?_⟩
  intro m hm
  refine ⟨fixedHalfKernelFamily_envelopes fallback P χ hχ hP m hm,?_⟩
  intro a b c L hL ha hb hc
  have hh : ((fixedHalfKernelFamily fallback P m hm a b c).cost:ℝ) ≤ (fallback a b c).cost := by
    exact_mod_cast fixedHalfKernelFamily_cost_le_fallback fallback P m hm a b c
  exact hh.trans (hFallback a b c L hL ha hb hc)

end
end HierarchicalAbsoluteSpectral
