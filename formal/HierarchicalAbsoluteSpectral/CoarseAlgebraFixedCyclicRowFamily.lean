import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedCyclicRowKernels

/-! One literal family supplies all six permutations in the symmetric
matrix-product envelope, as well as the existing core and output bounds. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms

theorem FixedRowKernelEnvelopes.mono {m : ℕ}
    {K : ∀ a b c : ℕ, ArithmeticKernel a b c} {χ χ' : ℝ}
    (hK : FixedRowKernelEnvelopes m K χ) (hχ : χ ≤ χ') :
    FixedRowKernelEnvelopes m K χ' := by
  have hbound (s : ℕ) : 8*χ*(s+m:ℕ)*(m:ℝ) ≤ 8*χ'*(s+m:ℕ)*(m:ℝ) := by gcongr
  constructor
  · intro a b c hb hc
    exact (hK.forward a b c hb hc).trans (hbound a)
  · intro a b c ha hc
    exact (hK.adjoint a b c ha hc).trans (hbound b)
  · intro a b c ha hb
    exact (hK.transpose_forward a b c ha hb).trans (hbound c)
  · intro a b c ha hc
    exact (hK.transpose_adjoint a b c ha hc).trans (hbound b)

structure FixedSixRowKernelEnvelopes (m : ℕ)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) : Prop
    extends FixedRowKernelEnvelopes m K χ where
  cyclic_forward : ∀ a b c : ℕ, b ≤ 2*width (1/2) m → c ≤ m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(a+m:ℕ)*(m:ℝ)
  cyclic_transpose : ∀ a b c : ℕ, a ≤ m → b ≤ 2*width (1/2) m →
    ((K a b c).cost:ℝ) ≤ 8*χ*(c+m:ℕ)*(m:ℝ)

theorem FixedSixRowKernelEnvelopes.of_cost_le {m : ℕ}
    {K P : ∀ a b c : ℕ, ArithmeticKernel a b c} {χ : ℝ}
    (hK : FixedSixRowKernelEnvelopes m K χ)
    (hP : ∀ a b c : ℕ, (P a b c).cost ≤ (K a b c).cost) :
    FixedSixRowKernelEnvelopes m P χ := by
  refine ⟨hK.toFixedRowKernelEnvelopes.of_cost_le hP,?_,?_⟩
  · intro a b c hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.cyclic_forward a b c hb hc)
  · intro a b c ha hb
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.cyclic_transpose a b c ha hb)

def fixedCyclicForwardCandidate
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (inner : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (m : ℕ) (hm : 0 < m) (a b c : ℕ) : ArithmeticKernel a b c :=
  if h : b ≤ 2*width (1/2) m ∧ c ≤ m then
    fixedCyclicHalfKernel inner a m c b hm h.2 h.1
  else fallback a b c

def fixedCyclicTransposeCandidate
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (inner : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (m : ℕ) (hm : 0 < m) (a b c : ℕ) : ArithmeticKernel a b c :=
  if h : a ≤ m ∧ b ≤ 2*width (1/2) m then
    (fixedCyclicHalfKernel inner c m a b hm h.1 h.2).transpose
  else fallback a b c

def fixedCyclicRowKernelFamily
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (inner : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (m : ℕ) (hm : 0 < m) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  fun a b c => (fallback a b c).cheaper
    ((fixedCyclicForwardCandidate fallback inner m hm a b c).cheaper
      (fixedCyclicTransposeCandidate fallback inner m hm a b c))

theorem fixedCyclicRowKernelFamily_cost_le_fallback
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (inner : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (m : ℕ) (hm : 0 < m) (a b c : ℕ) :
    (fixedCyclicRowKernelFamily fallback inner m hm a b c).cost ≤ (fallback a b c).cost :=
  ArithmeticKernel.cheaper_cost_le_left _ _

theorem fixedCyclicRowKernelFamily_envelopes
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (inner : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (χ : ℕ → ℝ) (hχ : ∀ m, 1 ≤ χ m)
    (hInner : ∀ m : ℕ, 1 ≤ m → ((inner m).cost:ℝ) ≤ (m:ℝ)^2*χ m)
    (m : ℕ) (hm : 0 < m) (hRows : FixedRowKernelEnvelopes m fallback (χ m)) :
    FixedSixRowKernelEnvelopes m (fixedCyclicRowKernelFamily fallback inner m hm) (χ m) := by
  have hmin (a b c : ℕ) :
      (fixedCyclicRowKernelFamily fallback inner m hm a b c).cost =
        min (fallback a b c).cost
          (min (fixedCyclicForwardCandidate fallback inner m hm a b c).cost
            (fixedCyclicTransposeCandidate fallback inner m hm a b c).cost) := by
    simp only [fixedCyclicRowKernelFamily, ArithmeticKernel.cheaper_cost]
  refine ⟨hRows.of_cost_le (fixedCyclicRowKernelFamily_cost_le_fallback fallback inner m hm),?_,?_⟩
  · intro a b c hb hc
    have hcost := fixedCyclicHalfKernel_cost inner χ hχ hInner a m c b hm hc hb
    have hcand :
        ((fixedCyclicForwardCandidate fallback inner m hm a b c).cost:ℝ) ≤
          8*χ m*(a+m:ℕ)*(m:ℝ) := by
      simpa only [fixedCyclicForwardCandidate, dif_pos (And.intro hb hc)] using hcost
    apply le_trans _ hcand
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans (min_le_left _ _)
  · intro a b c ha hb
    have hcost := fixedCyclicHalfKernel_cost inner χ hχ hInner c m a b hm ha hb
    have hcand :
        ((fixedCyclicTransposeCandidate fallback inner m hm a b c).cost:ℝ) ≤
          8*χ m*(c+m:ℕ)*(m:ℝ) := by
      simpa only [fixedCyclicTransposeCandidate, dif_pos (And.intro ha hb),
        ArithmeticKernel.transpose_cost] using hcost
    apply le_trans _ hcand
    exact_mod_cast hmin a b c ▸ (min_le_right _ _).trans (min_le_right _ _)

/-- All six row orientations and every earlier hierarchy/output guarantee
hold for one fixed circuit family and one subpolynomial row overhead. -/
theorem exists_fixed_six_family_kernel (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c)
      (χ χOut : ℕ → ℝ) (C : ℝ),
      0 < C ∧ (∀ m, 1 ≤ χ m) ∧ (∀ N, 1 ≤ χOut N) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, χOut N ≤ (N:ℝ)^ε) ∧
      ∀ (N m : ℕ) (hm : 0 < m), m ≤ N →
        FixedFamilyKernelEnvelopes ζ N m (K N m hm) (χ m) (χOut N) C ∧
        FixedSixRowKernelEnvelopes m (K N m hm) (χ m) := by
  obtain ⟨base,χb,χOut,C,hC,hχb,hχOut,hSubb,hOutSub,hBase⟩ := exists_fixed_family_kernel ζ hζ
  obtain ⟨inner,χi,hχi,hInner,hSubi⟩ := exists_fixed_dense_output_kernel_subpolynomial
  let χ := fun m => max (χb m) (χi m)
  have hχ (m : ℕ) : 1 ≤ χ m := (hχb m).trans (le_max_left _ _)
  have hInner' (m : ℕ) (hm : 1 ≤ m) : ((inner m).cost:ℝ) ≤ (m:ℝ)^2*χ m :=
    (hInner m hm).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))
  refine ⟨fun N m hm => fixedCyclicRowKernelFamily (base N m hm) inner m hm,
    χ,χOut,C,hC,hχ,hχOut,?_,hOutSub,?_⟩
  · intro ε hε
    filter_upwards [hSubb ε hε,hSubi ε hε] with m hb hi
    exact max_le hb hi
  · intro N m hm hNm
    have hB := hBase N m hm hNm
    have hRows := hB.row.mono (show χb m ≤ χ m from le_max_left _ _)
    have hB' : FixedFamilyKernelEnvelopes ζ N m (base N m hm) (χ m) (χOut N) C :=
      ⟨hRows,hB.core,hB.«classical»,hB.output⟩
    exact ⟨hB'.of_cost_le (fixedCyclicRowKernelFamily_cost_le_fallback (base N m hm) inner m hm),
      fixedCyclicRowKernelFamily_envelopes (base N m hm) inner χ hχ hInner' m hm hRows⟩

end
end HierarchicalAbsoluteSpectral
