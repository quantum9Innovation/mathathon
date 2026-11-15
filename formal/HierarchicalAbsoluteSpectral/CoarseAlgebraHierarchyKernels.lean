import HierarchicalAbsoluteSpectral.CoarseAlgebraRowKernels
import HierarchicalAbsoluteSpectral.CoarseAlgebraProjectedInertiaCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matmul.RectangularPrograms

def hierarchyKernelCaps {κ : ℝ}
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (N m : ℕ) (hm : 0 < m) : List MatrixKernelCap :=
  let F := blockedForwardKernel outer N m (width κ m) hm le_rfl
  let A := blockedAdjointKernel outer N m (width κ m) hm le_rfl
  [⟨N,m,width κ m,F⟩,⟨m,N,width κ m,A⟩,
    ⟨width κ m,m,N,F.transpose⟩,⟨width κ m,N,m,A.transpose⟩,
    ⟨N,width (1/2) N,N,inner N⟩]

def hierarchyArithmeticKernels {κ : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m))
    (inner : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N)
    (N m : ℕ) (hm : 0 < m) : ∀ a b c : ℕ, ArithmeticKernel a b c :=
  rowSensitiveKernelFamily
    (combineKernelCaps fallback (hierarchyKernelCaps outer inner N m hm)) outer m hm

/-- Simultaneous envelopes for the single kernel family passed to every
hierarchy compiler. All five orientations are actual circuit candidates. -/
structure HierarchyKernelEnvelopes (κ η ζ : ℝ) (N m : ℕ)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ) : Prop where
  core : ∀ a b c L : ℕ, 1 ≤ L → a ≤ L → b ≤ L → c ≤ L →
    ((K a b c).cost:ℝ) ≤ C*(L:ℝ)^(9/4+ζ)
  forward : ∀ a b c : ℕ, a ≤ N → b ≤ m → c ≤ width κ m →
    ((K a b c).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η)
  adjoint : ∀ a b c : ℕ, a ≤ m → b ≤ N → c ≤ width κ m →
    ((K a b c).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η)
  transpose_forward : ∀ a b c : ℕ, a ≤ width κ m → b ≤ m → c ≤ N →
    ((K a b c).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η)
  transpose_adjoint : ∀ a b c : ℕ, a ≤ width κ m → b ≤ N → c ≤ m →
    ((K a b c).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η)
  dense_output : ∀ a b c : ℕ, a ≤ N → b ≤ width (1/2) N → c ≤ N →
    ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^(2+ζ)
  stored_forward : ∀ a b c : ℕ, b ≤ m → c ≤ width κ m →
    ((K a b c).cost:ℝ) ≤ C*(a+m:ℕ)*(m:ℝ)^(1+η)
  stored_adjoint : ∀ a b c : ℕ, a ≤ m → c ≤ width κ m →
    ((K a b c).cost:ℝ) ≤ C*(b+m:ℕ)*(m:ℝ)^(1+η)
  stored_transpose_forward : ∀ a b c : ℕ, a ≤ width κ m → b ≤ m →
    ((K a b c).cost:ℝ) ≤ C*(c+m:ℕ)*(m:ℝ)^(1+η)
  stored_transpose_adjoint : ∀ a b c : ℕ, a ≤ width κ m → c ≤ m →
    ((K a b c).cost:ℝ) ≤ C*(b+m:ℕ)*(m:ℝ)^(1+η)

theorem exists_uniform_hierarchy_arithmetic_kernels (η ζ : ℝ) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ (κ : ℝ) (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ),
      1/2 < κ ∧ κ ≤ 1 ∧ 0 < C ∧ ∀ (N m : ℕ) (hm : 0 < m), m ≤ N →
        HierarchyKernelEnvelopes κ η ζ N m (K N m hm) C := by
  obtain ⟨fallback,Cf,hCf,hFallback⟩ := exists_full_shape_arithmetic_kernels ζ hζ
  obtain ⟨κ,outer,Ca,hκ,hκ1,hCa,hOuter⟩ := exists_growing_input_optimal_arithmetic_kernels η hη
  obtain ⟨inner,Co,hCo,hInner⟩ := exists_half_rectangular_arithmetic_kernels ζ hζ
  let C := Cf+Ca+Co+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfC : Cf ≤ C := by dsimp [C]; linarith
  have haC : Ca ≤ C := by dsimp [C]; linarith
  have hoC : Co ≤ C := by dsimp [C]; linarith
  refine ⟨κ,hierarchyArithmeticKernels fallback outer inner,C,hκ,hκ1,hC,?_⟩
  intro N m hm hNm
  have hN : 1 ≤ N := by omega
  let caps := hierarchyKernelCaps outer inner N m hm
  let F := blockedForwardKernel outer N m (width κ m) hm le_rfl
  let A := blockedAdjointKernel outer N m (width κ m) hm le_rfl
  have hFA := hOuter N m (width κ m) hm hNm le_rfl
  have hF : (F.cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) := hFA.1.trans (by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact mul_le_mul_of_nonneg_right haC (Nat.cast_nonneg _))
  have hA : (A.cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) := hFA.2.trans (by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact mul_le_mul_of_nonneg_right haC (Nat.cast_nonneg _))
  have hI : ((inner N).cost:ℝ) ≤ C*(N:ℝ)^(2+ζ) := (hInner N hN).trans
    (mul_le_mul_of_nonneg_right hoC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hcap (cap : MatrixKernelCap) (hmem : cap ∈ caps) (a b c : ℕ)
      (hfit : cap.Fits a b c) :
      ((hierarchyArithmeticKernels fallback outer inner N m hm a b c).cost:ℝ) ≤ cap.kernel.cost := by
    exact_mod_cast (rowSensitiveKernelFamily_cost_le_fallback
      (combineKernelCaps fallback caps) outer m hm a b c).trans
        (combineKernelCaps_cost_le_cap fallback caps cap hmem a b c hfit)
  have hrow := rowSensitiveKernelFamily_row_bounds
    (combineKernelCaps fallback caps) outer hCa.le hOuter m hm
  have hrowC (z : ℕ) : Ca*(z:ℝ)*(m:ℝ)^(1+η) ≤ C*(z:ℝ)*(m:ℝ)^(1+η) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact mul_le_mul_of_nonneg_right haC (Nat.cast_nonneg _)
  constructor
  · intro a b c L hL ha hb hc
    have hh : ((hierarchyArithmeticKernels fallback outer inner N m hm a b c).cost:ℝ) ≤
        ((fallback a b c).cost:ℝ) := by
      exact_mod_cast (rowSensitiveKernelFamily_cost_le_fallback
        (combineKernelCaps fallback caps) outer m hm a b c).trans
          (combineKernelCaps_cost_le_fallback fallback caps a b c)
    exact hh.trans ((hFallback a b c L hL ha hb hc).trans
      (mul_le_mul_of_nonneg_right hfC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  · intro a b c ha hb hc
    exact (hcap ⟨N,m,width κ m,F⟩ (by simp [caps,hierarchyKernelCaps,F]) a b c ⟨ha,hb,hc⟩).trans hF
  · intro a b c ha hb hc
    exact (hcap ⟨m,N,width κ m,A⟩ (by simp [caps,hierarchyKernelCaps,A]) a b c ⟨ha,hb,hc⟩).trans hA
  · intro a b c ha hb hc
    have hh := hcap ⟨width κ m,m,N,F.transpose⟩
      (by simp [caps,hierarchyKernelCaps,F]) a b c ⟨ha,hb,hc⟩
    simpa only [ArithmeticKernel.transpose_cost] using hh.trans (by simpa using hF)
  · intro a b c ha hb hc
    have hh := hcap ⟨width κ m,N,m,A.transpose⟩
      (by simp [caps,hierarchyKernelCaps,A]) a b c ⟨ha,hb,hc⟩
    simpa only [ArithmeticKernel.transpose_cost] using hh.trans (by simpa using hA)
  · intro a b c ha hb hc
    exact (hcap ⟨N,width (1/2) N,N,inner N⟩
      (by simp [caps,hierarchyKernelCaps]) a b c ⟨ha,hb,hc⟩).trans hI
  · intro a b c hb hc
    exact ((hrow a b c).1 hb hc).trans (hrowC (a+m))
  · intro a b c ha hc
    exact ((hrow a b c).2.1 ha hc).trans (hrowC (b+m))
  · intro a b c ha hb
    exact ((hrow a b c).2.2.1 ha hb).trans (hrowC (c+m))
  · intro a b c ha hc
    exact ((hrow a b c).2.2.2 ha hc).trans (hrowC (b+m))

end
end HierarchicalAbsoluteSpectral
