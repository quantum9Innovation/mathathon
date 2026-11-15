import HierarchicalAbsoluteSpectral.BaseOperational
import HierarchicalAbsoluteSpectral.CholeskyCost

/-! An unconditional fast arithmetic implementation of the finite base,
including both factorizations and every inverse used by Newton iteration. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

theorem baseConstructionCost_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (n : ℕ) (hn : 1 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64) :
    (baseConstructionCost kernels n h hh:ℝ) ≤
      40*(C+1)*(n:ℝ)^p*(1+4*Real.log (1/(4*h))) := by
  let N := (n:ℝ)^p
  let L := 1+4*Real.log (1/(4*h))
  have hnp : 0 ≤ N := Real.rpow_nonneg (by positivity) _
  have hn1 : 1 ≤ N := Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hsq : (n:ℝ)*(n:ℝ) ≤ N := by
    simpa only [Real.rpow_two, pow_two] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) hp
  have hlog : 0 ≤ Real.log (1/(4*h)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity : 0 < 4*h)).mpr
    linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hchol := choleskyCost_bound kernels C p hC hp hK n hn
  have hkernel := hK n n n n (by simpa using hn) hn le_rfl le_rfl le_rfl
  have hq := baseNewtonSteps_bound h hh hh'
  change (choleskyCost kernels n:ℝ) ≤ 9*(C+1)*N at hchol
  change ((kernels n n n).cost:ℝ) ≤ C*N at hkernel
  change (baseNewtonSteps h hh:ℝ) ≤ L at hq
  have hfixed : 2*(choleskyCost kernels n:ℝ)+5*((kernels n n n).cost:ℝ)+2+2*(n:ℝ)*(n:ℝ) ≤
      23*(C+1)*N := by nlinarith
  have hstep : (choleskyCost kernels n:ℝ)+2*((kernels n n n).cost:ℝ)+2*(n:ℝ)*(n:ℝ) ≤
      11*(C+1)*N := by nlinarith
  have hloop := mul_le_mul hq hstep (by positivity : (0:ℝ) ≤
      (choleskyCost kernels n:ℝ)+2*((kernels n n n).cost:ℝ)+2*(n:ℝ)*(n:ℝ)) (by linarith : 0 ≤ L)
  have hfixed' : 23*(C+1)*N ≤ L*(23*(C+1)*N) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ 23*(C+1)*N)
  have hlast : L*(23*(C+1)*N)+L*(11*(C+1)*N) ≤ 40*(C+1)*N*L := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ L) (mul_nonneg (by linarith : 0 ≤ C+1) hnp)]
  have hsum := (add_le_add hfixed hloop).trans ((add_le_add hfixed' le_rfl).trans hlast)
  simpa only [baseConstructionCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hsum

theorem exists_fast_base_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (D K0 : Core n) (hD : D.PosDef) (hK0 : K0ᵀ = K0)
        (h : ℝ) (hh : 0 < h), h ≤ 1/64 → 1 ≤ n →
        (baseConstructionProgram kernels D K0 hD hK0 h hh).admissible ∧
        ((baseConstructionProgram kernels D K0 hD hK0 h hh).work:ℝ) ≤
          C*(n:ℝ)^(9/4+ζ)*(1+4*Real.log (1/(4*h))) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,40*(C+1),by positivity,?_⟩
  intro n D K0 hD hK0 h hh hh' hn
  refine ⟨baseConstructionProgram_admissible kernels D K0 hD hK0 h hh,?_⟩
  rw [baseConstructionProgram_work]
  apply baseConstructionCost_bound kernels C (9/4+ζ) hC (by linarith) _ n hn h hh hh'
  intro a b c N hm _hN ha hb hc
  apply (hK a b c hm).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  exact_mod_cast max_le ha (max_le hb hc)

end
end HierarchicalAbsoluteSpectral
