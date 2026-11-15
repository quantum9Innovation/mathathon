import HierarchicalAbsoluteSpectral.CoarseAlgebraTransposeKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.RectangularPrograms

def denseOutputKernel {κ : ℝ}
    (K : ∀ N : ℕ, ArithmeticKernel N (width κ N) N)
    (N n r p : ℕ) (hn : n ≤ N) (hr : r ≤ width κ N) (hp : p ≤ N) :
    ArithmeticKernel n r p :=
  (K N).padShape (Fin.castLEEmb hn) (Fin.castLEEmb hr) (Fin.castLEEmb hp)

@[simp] theorem denseOutputKernel_cost {κ : ℝ}
    (K : ∀ N : ℕ, ArithmeticKernel N (width κ N) N)
    (N n r p : ℕ) (hn : n ≤ N) (hr : r ≤ width κ N) (hp : p ≤ N) :
    (denseOutputKernel K N n r p hn hr hp).cost = (K N).cost := by
  simp [denseOutputKernel]

theorem exists_dense_output_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (K : ∀ N : ℕ, ArithmeticKernel N (width (1/2) N) N) (C : ℝ), 0 < C ∧
      ∀ (N n r p : ℕ) (hN : 1 ≤ N) (hn : n ≤ N)
        (hr : r ≤ width (1/2) N) (hp : p ≤ N),
        ((denseOutputKernel K N n r p hn hr hp).cost:ℝ) ≤ C*(N:ℝ)^(2+ζ) := by
  obtain ⟨K,C,hC,hK⟩ := exists_half_rectangular_arithmetic_kernels ζ hζ
  refine ⟨K,C,hC,?_⟩
  intro N n r p hN hn hr hp
  simpa only [denseOutputKernel_cost] using hK N hN

theorem sqrt_rank_fits_outer_width (κ : ℝ) (hκ : 1/2 ≤ κ)
    (m N r : ℕ) (hm : 1 ≤ m) (hNm : m ≤ N)
    (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) : r ≤ width κ N := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hN : (1:ℝ) ≤ N := hmR.trans hNmR
  have hroot := Real.sqrt_le_sqrt hNmR
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hκ
  have hb : (r:ℝ) ≤ (N:ℝ)^κ := by
    rw [← Real.sqrt_eq_rpow] at hpow
    exact hr.trans (hroot.trans hpow)
  exact_mod_cast hb.trans (Nat.le_ceil ((N:ℝ)^κ))

end
end HierarchicalAbsoluteSpectral
