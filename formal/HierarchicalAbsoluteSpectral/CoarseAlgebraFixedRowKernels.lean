import HierarchicalAbsoluteSpectral.CoarseAlgebraColumnKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.RectangularPrograms Filter

def fixedHalfForwardKernel
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m))
    (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ArithmeticKernel s k b :=
  (((K m).blockColumns 2).tall (max s m) hm).padShape
    (Fin.castLEEmb (le_max_left _ _)) (Fin.castLEEmb hk) (Fin.castLEEmb hb)

def fixedHalfAdjointKernel
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m))
    (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ArithmeticKernel k s b :=
  (((K m).blockColumns 2).longInner (max s m) hm).padShape
    (Fin.castLEEmb hk) (Fin.castLEEmb (le_max_left _ _)) (Fin.castLEEmb hb)

theorem fixedHalf_row_kernel_bounds
    (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m))
    (χ : ℕ → ℝ) (hχ : ∀ m, 1 ≤ χ m)
    (hK : ∀ m : ℕ, 1 ≤ m → ((K m).cost:ℝ) ≤ (m:ℝ)^2*χ m)
    (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((fixedHalfForwardKernel K s m k b hm hk hb).cost:ℝ) ≤
      8*χ m*(s+m:ℕ)*(m:ℝ) ∧
    ((fixedHalfAdjointKernel K s m k b hm hk hb).cost:ℝ) ≤
      8*χ m*(s+m:ℕ)*(m:ℝ) := by
  let N := max s m
  let P := (K m).blockColumns 2
  have hNm : m ≤ N := le_max_right _ _
  have hNadd : (N:ℝ) ≤ (s+m:ℕ) := by exact_mod_cast (show max s m ≤ s+m by omega)
  have hχ0 : 0 ≤ χ m := le_trans (by norm_num) (hχ m)
  have hP : (P.cost:ℝ) ≤ (2*χ m)*(m:ℝ)^(2:ℝ) := by
    have hc := hK m hm
    dsimp [P]
    rw [ArithmeticKernel.blockColumns_cost,Nat.cast_mul,Nat.cast_ofNat,Real.rpow_two]
    nlinarith
  have hF := P.tall_cost_bound N hm hNm (2*χ m) 2 (by positivity) hP
  have hA := P.longInner_cost_bound N hm hNm (2*χ m) 2 (by positivity) hP
  norm_num only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one] at hF hA
  have hwidth : (width (1/2) m:ℝ) ≤ m := by exact_mod_cast half_width_le m hm
  have hsum : 2*(N:ℝ)*(2*width (1/2) m:ℕ) ≤ 4*χ m*(N:ℝ)*(m:ℝ) := by
    have hw := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 4*(N:ℝ) by positivity)
    have hc := mul_le_mul_of_nonneg_right (hχ m) (show 0 ≤ 4*(N:ℝ)*(m:ℝ) by positivity)
    push_cast
    nlinarith
  have hlast : 8*χ m*(N:ℝ)*(m:ℝ) ≤ 8*χ m*(s+m:ℕ)*(m:ℝ) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNadd (by positivity)) (Nat.cast_nonneg _)
  constructor
  · simp only [fixedHalfForwardKernel,ArithmeticKernel.padShape_cost]
    apply hF.trans
    apply le_trans _ hlast
    nlinarith [mul_nonneg (mul_nonneg hχ0 (Nat.cast_nonneg (max s m))) (Nat.cast_nonneg m)]
  · simp only [fixedHalfAdjointKernel,ArithmeticKernel.padShape_cost]
    apply hA.trans
    apply le_trans _ hlast
    nlinarith

theorem exists_fixed_row_kernels_subpolynomial :
    ∃ (K : ∀ m : ℕ, ArithmeticKernel m m (width (1/2) m)) (χ : ℕ → ℝ),
      (∀ m, 1 ≤ χ m) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m:ℝ)^ε) ∧
      ∀ (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m),
        ((fixedHalfForwardKernel K s m k b hm hk hb).cost:ℝ) ≤ 8*χ m*(s+m:ℕ)*(m:ℝ) ∧
        ((fixedHalfAdjointKernel K s m k b hm hk hb).cost:ℝ) ≤ 8*χ m*(s+m:ℕ)*(m:ℝ) := by
  obtain ⟨K,χ,hχ,hK,hsub⟩ := exists_fixed_half_kernel_subpolynomial
  exact ⟨K,χ,hχ,hsub,fixedHalf_row_kernel_bounds K χ hχ hK⟩

end
end HierarchicalAbsoluteSpectral
