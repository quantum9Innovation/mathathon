import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSupportSpectral
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearch
import HierarchicalAbsoluteSpectral.ThresholdSearchCap
import Mathlib.Algebra.Order.Floor.Semiring

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

/-- The bisection count is logarithmic in dimension and requested accuracy,
with no leading-to-target singular-value ratio. -/
theorem exactGramAppendixSearchCap_le_clog (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    exactGramAppendixSearchCap k ε hε ≤ Nat.clog 2 ⌈(k:ℝ)^2/ε⌉₊ := by
  apply leastHalvings_le
  have hceil : (k:ℝ)^2/ε ≤ (⌈(k:ℝ)^2/ε⌉₊:ℝ) := Nat.le_ceil _
  have hpGeneric (M : ℕ) : (M:ℝ) ≤ (2:ℝ)^(Nat.clog 2 M) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) M
  have hp : (⌈(k:ℝ)^2/ε⌉₊:ℝ) ≤ (2:ℝ)^(Nat.clog 2 ⌈(k:ℝ)^2/ε⌉₊) := by
    exact hpGeneric _
  have hmul := (div_le_iff₀ hε).mp (hceil.trans hp)
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ) < 2) _)).mpr
  nlinarith

theorem exactGramAppendixSearchCap_mono (k m : ℕ) (hkm : k ≤ m) (ε : ℝ) (hε : 0 < ε) :
    exactGramAppendixSearchCap k ε hε ≤ exactGramAppendixSearchCap m ε hε := by
  apply leastHalvings_mono
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hm : (k:ℝ) ≤ m := by exact_mod_cast hkm
  nlinarith

theorem exactGramAppendix_draws_le (k m : ℕ) (hkm : k ≤ m) (ε : ℝ) (hε : 0 < ε) :
    exactGramAppendixSearchGaussianDraws k ε hε+1+k*k ≤
      exactGramAppendixSearchCap m ε hε*(m*m)+1+m*m := by
  unfold exactGramAppendixSearchGaussianDraws
  have hc := exactGramAppendixSearchCap_mono k m hkm ε hε
  gcongr

/-- The appendix uses two relative factors before taking a scalar square
root: one from exact bisection and one from the fresh random shift. -/
theorem exactGramAppendix_sqrt_budget (eigenvalue σ u t ε : ℝ)
    (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (heigen : eigenvalue = σ^2)
    (hu : u ≤ (1+ε)*eigenvalue) (ht : t ≤ (1+ε)*u) :
    Real.sqrt t ≤ (1+ε)*σ := by
  apply (Real.sqrt_le_left (mul_nonneg (by linarith) hσ)).mpr
  have hh := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ 1+ε)
  rw [heigen] at hh
  nlinarith

theorem exactGramAppendix_core_charpoly_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {k : ℕ} (H : Core k) (m : ℕ) (hkm : k ≤ m) :
    ((exactGramCharpolyProgram kernels H).work:ℝ) ≤
      33*(C+1)*(Nat.clog 2 (m+1)+1:ℕ)*((2*(m+1):ℕ):ℝ)^q := by
  apply (exactGramCharpolyProgram_work_bound kernels C q hC hq hK H).trans
  have hlog : Nat.clog 2 (k+1) ≤ Nat.clog 2 (m+1) := Nat.clog_monotone 2 (by omega)
  have hpow : ((2*(k+1):ℕ):ℝ)^q ≤ ((2*(m+1):ℕ):ℝ)^q :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 (Nat.add_le_add_right hkm 1))
      (by linarith)
  gcongr

end
end HierarchicalAbsoluteSpectral
