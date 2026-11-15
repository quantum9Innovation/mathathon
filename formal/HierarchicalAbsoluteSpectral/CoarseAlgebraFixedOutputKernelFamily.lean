import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedOutputKernel
import HierarchicalAbsoluteSpectral.CoarseAlgebraDominatedKernelFamily

/-! A single literal family retains the fixed row, core, and classical
bounds while offering the actual dense-output circuit as another candidate. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms

def fixedOutputKernelCaps
    (outer : ∀ N : ℕ, ArithmeticKernel N N (width (1/2) N))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (N : ℕ) : List MatrixKernelCap :=
  [⟨N,N,width (1/2) N,outer N⟩,
    ⟨width (1/2) N,N,N,(outer N).transpose⟩,
    ⟨N,width (1/2) N,N,inner N⟩]

def fixedOutputKernelFamily
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ N : ℕ, ArithmeticKernel N N (width (1/2) N))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (N : ℕ) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  combineKernelCaps fallback (fixedOutputKernelCaps outer inner N)

theorem fixedOutputKernelFamily_cost_le_fallback
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ N : ℕ, ArithmeticKernel N N (width (1/2) N))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (N a b c : ℕ) :
    (fixedOutputKernelFamily fallback outer inner N a b c).cost ≤ (fallback a b c).cost :=
  combineKernelCaps_cost_le_fallback fallback (fixedOutputKernelCaps outer inner N) a b c

structure FixedOutputKernelEnvelopes (N : ℕ)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χOut : ℝ) : Prop where
  outer : ∀ a b c : ℕ, a ≤ N → b ≤ N → c ≤ width (1/2) N →
    ((K a b c).cost:ℝ) ≤ (N:ℝ)^2*χOut
  transpose_outer : ∀ a b c : ℕ, a ≤ width (1/2) N → b ≤ N → c ≤ N →
    ((K a b c).cost:ℝ) ≤ (N:ℝ)^2*χOut
  dense_output : ∀ a b c : ℕ, a ≤ N → b ≤ width (1/2) N → c ≤ N →
    ((K a b c).cost:ℝ) ≤ (N:ℝ)^2*χOut

theorem fixedOutputKernelFamily_envelopes
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ N : ℕ, ArithmeticKernel N N (width (1/2) N))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (χOut : ℕ → ℝ)
    (hK : ∀ N : ℕ, 1 ≤ N →
      ((outer N).cost:ℝ) ≤ (N:ℝ)^2*χOut N ∧
      ((inner N).cost:ℝ) ≤ (N:ℝ)^2*χOut N)
    (N : ℕ) (hN : 1 ≤ N) :
    FixedOutputKernelEnvelopes N (fixedOutputKernelFamily fallback outer inner N) (χOut N) := by
  have hcap (cap : MatrixKernelCap) (hmem : cap ∈ fixedOutputKernelCaps outer inner N)
      (a b c : ℕ) (hfit : cap.Fits a b c) :
      ((fixedOutputKernelFamily fallback outer inner N a b c).cost:ℝ) ≤ cap.kernel.cost := by
    exact_mod_cast combineKernelCaps_cost_le_cap fallback
      (fixedOutputKernelCaps outer inner N) cap hmem a b c hfit
  constructor
  · intro a b c ha hb hc
    exact (hcap ⟨N,N,width (1/2) N,outer N⟩
      (by simp [fixedOutputKernelCaps]) a b c ⟨ha,hb,hc⟩).trans (hK N hN).1
  · intro a b c ha hb hc
    have hh := hcap ⟨width (1/2) N,N,N,(outer N).transpose⟩
      (by simp [fixedOutputKernelCaps]) a b c ⟨ha,hb,hc⟩
    exact hh.trans (by simpa only [ArithmeticKernel.transpose_cost] using (hK N hN).1)
  · intro a b c ha hb hc
    exact (hcap ⟨N,width (1/2) N,N,inner N⟩
      (by simp [fixedOutputKernelCaps]) a b c ⟨ha,hb,hc⟩).trans (hK N hN).2

theorem FixedOutputKernelEnvelopes.of_cost_le {N : ℕ}
    {K P : ∀ a b c : ℕ, ArithmeticKernel a b c} {χOut : ℝ}
    (hK : FixedOutputKernelEnvelopes N K χOut)
    (hP : ∀ a b c : ℕ, (P a b c).cost ≤ (K a b c).cost) :
    FixedOutputKernelEnvelopes N P χOut := by
  constructor
  · intro a b c ha hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.outer a b c ha hb hc)
  · intro a b c ha hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.transpose_outer a b c ha hb hc)
  · intro a b c ha hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.dense_output a b c ha hb hc)

/-- The actual output rank pads into the fixed ambient half-width circuit. -/
theorem FixedOutputKernelEnvelopes.sqrt_rank {N : ℕ}
    {K : ∀ a b c : ℕ, ArithmeticKernel a b c} {χOut : ℝ}
    (hK : FixedOutputKernelEnvelopes N K χOut)
    (n m r p : ℕ) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N)
    (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) (hp : p ≤ N) :
    ((K n r p).cost:ℝ) ≤ (N:ℝ)^2*χOut :=
  hK.dense_output n r p hn
    (sqrt_rank_fits_outer_width (1/2) le_rfl m N r hm hNm hr) hp

structure FixedFamilyKernelEnvelopes (ζ : ℝ) (N m : ℕ)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ χOut C : ℝ) : Prop where
  row : FixedRowKernelEnvelopes m K χ
  core : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
    ((K a b c).cost:ℝ) ≤ C*(D:ℝ)^(9/4+ζ)
  «classical» : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c
  output : FixedOutputKernelEnvelopes N K χOut

theorem FixedFamilyKernelEnvelopes.of_cost_le {ζ χ χOut C : ℝ} {N m : ℕ}
    {K P : ∀ a b c : ℕ, ArithmeticKernel a b c}
    (hK : FixedFamilyKernelEnvelopes ζ N m K χ χOut C)
    (hP : ∀ a b c : ℕ, (P a b c).cost ≤ (K a b c).cost) :
    FixedFamilyKernelEnvelopes ζ N m P χ χOut C := by
  refine ⟨hK.row.of_cost_le hP,?_,?_,hK.output.of_cost_le hP⟩
  · intro a b c D hD ha hb hc
    exact (Nat.cast_le.mpr (hP a b c)).trans (hK.core a b c D hD ha hb hc)
  · intro a b c
    exact (hP a b c).trans (hK.«classical» a b c)

theorem FixedFamilyKernelEnvelopes.wide_work {ζ χ χOut C : ℝ} {N m : ℕ}
    {K : ∀ a b c : ℕ, ArithmeticKernel a b c}
    (hK : FixedFamilyKernelEnvelopes ζ N m K χ χOut C)
    {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) (ha : 1 ≤ a) :
    (orthogonalRangeProgram K Y).work ≤ 22*a*b*b :=
  dominated_orthogonalRangeProgram_work K hK.«classical» Y ha

/-- The family is chosen before the exponent in either subpolynomial bound.
Its finite circuit minimum preserves every bound for the same algorithm. -/
theorem exists_fixed_family_kernel (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c)
      (χ χOut : ℕ → ℝ) (C : ℝ),
      0 < C ∧ (∀ m, 1 ≤ χ m) ∧ (∀ N, 1 ≤ χOut N) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, χOut N ≤ (N:ℝ)^ε) ∧
      ∀ (N m : ℕ) (hm : 0 < m), m ≤ N →
        FixedFamilyKernelEnvelopes ζ N m (K N m hm) (χ m) (χOut N) C := by
  obtain ⟨base,χ,C,hC,hχ,hSub,hBase⟩ :=
    exists_fixed_classically_dominated_hierarchy_kernel_family ζ hζ
  obtain ⟨outer,inner,χOut,hχOut,hOut,hOutSub⟩ :=
    exists_fixed_half_output_kernels_subpolynomial
  refine ⟨fun N m hm => fixedOutputKernelFamily (base m hm) outer inner N,
    χ,χOut,C,hC,hχ,hχOut,hSub,hOutSub,?_⟩
  intro N m hm hNm
  have hle := fixedOutputKernelFamily_cost_le_fallback (base m hm) outer inner N
  have hB := hBase m hm
  constructor
  · exact hB.1.of_cost_le hle
  · intro a b c D hD ha hb hc
    exact (Nat.cast_le.mpr (hle a b c)).trans (hB.2.1 a b c D hD ha hb hc)
  · intro a b c
    exact (hle a b c).trans (hB.2.2 a b c)
  · exact fixedOutputKernelFamily_envelopes (base m hm) outer inner χOut hOut N (by omega)

end
end HierarchicalAbsoluteSpectral
