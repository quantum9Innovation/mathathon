import HierarchicalAbsoluteSpectral.BaseMainTotalCost
import HierarchicalAbsoluteSpectral.ProbabilityInitializerCorrectness

/-! Uniform numerical core-algebra bounds for a support dimension at most
the original core size.  Zero support dimensions and zero deflated ranks
are included. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L k s t : ℕ}

theorem baseFixedKernelEnvelope_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    (kernelEnvelope K k:ℝ) ≤ C*(N:ℝ)^e := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset
    (Fin (k+1) × Fin (k+1) × Fin (k+1))) Finset.univ_nonempty (kernelEnvelopeEntry K k)
  change ((Finset.univ.sup (kernelEnvelopeEntry K k):ℕ):ℝ) ≤ _
  rw [hi]
  unfold kernelEnvelopeEntry
  split_ifs with hz
  · simp only [Nat.cast_zero]
    positivity
  · exact hK _ _ _ N hN (by omega) (by omega) (by omega)

theorem baseFixedPSDGramCost_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    (psdGramCost K k:ℝ) ≤ 9*(C+1)*(N:ℝ)^e := by
  by_cases hk1 : 1 ≤ k
  · apply (psdGramCost_bound K C e hC he (fun a b c N _ => hK a b c N) k hk1).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) (by linarith)) (by positivity)
  · have hk0 : k = 0 := by omega
    rw [hk0,psdGramCost]
    simp only [Nat.cast_zero]
    positivity

theorem baseFixedCholeskyCost_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    (choleskyCost K k:ℝ) ≤ 9*(C+1)*(N:ℝ)^e := by
  by_cases hk1 : 1 ≤ k
  · apply (choleskyCost_bound K C e hC he (fun a b c N _ => hK a b c N) k hk1).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) (by linarith)) (by positivity)
  · have hk0 : k = 0 := by omega
    rw [hk0,choleskyCost]
    simp only [Nat.cast_zero]
    positivity

theorem baseFixedCore_square_bound (e : ℝ) (he : 2 ≤ e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) : (k:ℝ)*(k:ℝ) ≤ (N:ℝ)^e := by
  have hs : (k:ℝ)*(k:ℝ) ≤ (N:ℝ)*(N:ℝ) := by exact_mod_cast Nat.mul_le_mul hk hk
  exact hs.trans (by simpa only [Real.rpow_two,pow_two] using
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ) ≤ N) he)

theorem baseFixedCore_linear_bound (e : ℝ) (he : 2 ≤ e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) : (k:ℝ) ≤ (N:ℝ)^e := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hkN : (k:ℝ) ≤ N := by exact_mod_cast hk
  have hs := baseFixedCore_square_bound e he N N hN le_rfl
  nlinarith

/-- Only the two actual Gram-product circuits remain outside the core
power; no accuracy ratio or polynomial degree multiplies their cost. -/
def baseFixedCoarseGramCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (m s t : ℕ) : ℕ := (K m s m).cost+(K m t m).cost

theorem coarseSupportWorkCap_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (m s t : ℕ) (hm : 1 ≤ m) :
    (coarseSupportWorkCap K m s t:ℝ) ≤
      baseFixedCoarseGramCost K m s t+11*(C+1)*(m:ℝ)^e := by
  have hp := baseFixedPSDGramCost_bound K C e hC he hK m m hm le_rfl
  have hk := baseFixedKernelEnvelope_bound K C e hC hK m m hm le_rfl
  have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ m) e
  unfold coarseSupportWorkCap baseFixedCoarseGramCost
  push_cast
  nlinarith

/-- A dimension-uniform cap for the exact expression used in the main
initializer branch.  The rank parameter may be zero. -/
def baseFixedInitializerWorkCap (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (k r : ℕ) : ℕ :=
  5*kernelEnvelope K k+psdGramCost K r+3*k*k+k+10

theorem baseFixedInitializerWorkCap_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k r N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) (hr : r ≤ N) :
    (baseFixedInitializerWorkCap K k r:ℝ) ≤ 25*(C+1)*(N:ℝ)^e := by
  have henv := baseFixedKernelEnvelope_bound K C e hC hK k N hN hk
  have hpsd := baseFixedPSDGramCost_bound K C e hC he hK r N hN hr
  have hsq := baseFixedCore_square_bound e he k N hN hk
  have hlin := baseFixedCore_linear_bound e he k N hN hk
  have hpow1 : 1 ≤ (N:ℝ)^e := Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hpow0 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) e
  unfold baseFixedInitializerWorkCap
  push_cast
  nlinarith [mul_nonneg hC.le hpow0]

theorem baseConstructionCost_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) (h : ℝ) (hh : 0 < h) :
    (baseConstructionCost K k h hh:ℝ) ≤
      (23+11*(baseNewtonSteps h hh:ℝ))*(C+1)*(N:ℝ)^e := by
  have hchol := baseFixedCholeskyCost_bound K C e hC he hK k N hN hk
  have hkernel := hK k k k N hN hk hk hk
  have hsq := baseFixedCore_square_bound e he k N hN hk
  have hpow1 : 1 ≤ (N:ℝ)^e := Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hpow0 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) e
  have hfixed : 2*(choleskyCost K k:ℝ)+5*(K k k k).cost+2+2*(k:ℝ)*k ≤
      23*(C+1)*(N:ℝ)^e := by nlinarith [mul_nonneg hC.le hpow0]
  have hstep : (choleskyCost K k:ℝ)+2*(K k k k).cost+2*(k:ℝ)*k ≤
      11*(C+1)*(N:ℝ)^e := by nlinarith
  have hloop := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (baseNewtonSteps h hh))
  unfold baseConstructionCost
  push_cast
  nlinarith only [hfixed,hloop]

theorem baseFixedSetupCost_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (k N d : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) (h : ℝ) (hh : 0 < h) :
    (baseConstructionCost K k h hh+2*k*k+d:ℕ) ≤
      (25+(d:ℝ)+11*(baseNewtonSteps h hh:ℝ))*(C+1)*(N:ℝ)^e := by
  have hb := baseConstructionCost_core_bound K C e hC he hK k N hN hk h hh
  have hsq := baseFixedCore_square_bound e he k N hN hk
  have hpow1 : 1 ≤ (N:ℝ)^e := Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hpow0 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) e
  have hscalar : 2*(k:ℝ)*k+(d:ℝ) ≤ (2+(d:ℝ))*(C+1)*(N:ℝ)^e := by
    have hd := mul_le_mul_of_nonneg_left hpow1 (Nat.cast_nonneg d)
    nlinarith [mul_nonneg hC.le hpow0,
      mul_nonneg (by positivity : (0:ℝ) ≤ d) (mul_nonneg hC.le hpow0)]
  push_cast
  nlinarith only [hb,hscalar]

end
end HierarchicalAbsoluteSpectral
