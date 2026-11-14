import HierarchicalAbsoluteSpectral.IdealMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Lagrange

/-!
The actual interpolation nodes and sampled inverse-root values in Lemma 4.
The definitions use nested nonnegative scalar square roots, field operations
and integer powers. Trigonometric functions occur only in the proofs that
these are exactly the Gauss--Chebyshev nodes.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial

def dyadicCos (s : ℕ) : ℝ := Real.sqrtTwoAddSeries 0 s / 2
def dyadicSin (s : ℕ) : ℝ := Real.sqrt (1 - (dyadicCos s)^2)
def dyadicRoot (s : ℕ) : ℂ := (dyadicCos s : ℂ) + (dyadicSin s : ℂ)*Complex.I
def dyadicNode (s j : ℕ) : ℝ := ((dyadicRoot s)^(2*j+1)).re

theorem dyadicCos_nonneg (s : ℕ) : 0 ≤ dyadicCos s := by
  exact div_nonneg (Real.sqrtTwoAddSeries_zero_nonneg s) (by norm_num)

theorem dyadicCos_lt_one (s : ℕ) : dyadicCos s < 1 := by
  have hs := Real.sqrtTwoAddSeries_lt_two s
  dsimp [dyadicCos]
  linarith

theorem dyadicSin_radicand_pos (s : ℕ) : 0 < 1 - (dyadicCos s)^2 := by
  have h0 := dyadicCos_nonneg s
  have h1 := dyadicCos_lt_one s
  nlinarith [mul_pos (sub_pos.mpr h1) (show 0 < 1+dyadicCos s by linarith)]

theorem dyadicRoot_eq_exp (s : ℕ) :
    dyadicRoot s = Complex.exp (((Real.pi / (2:ℝ)^(s+1) : ℝ) : ℂ)*Complex.I) := by
  let θ : ℝ := Real.pi / (2:ℝ)^(s+1)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ' : θ ≤ Real.pi := by
    dsimp [θ]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(s+1))).mpr
    have hs : (1:ℝ) ≤ 2^(s+1) := one_le_pow₀ (by norm_num)
    nlinarith [Real.pi_pos]
  have hc : dyadicCos s = Real.cos θ := (Real.cos_pi_over_two_pow s).symm
  have hsin : dyadicSin s = Real.sin θ := by
    rw [dyadicSin, hc]
    exact (Real.sin_eq_sqrt_one_sub_cos_sq hθ hθ').symm
  rw [dyadicRoot, hc, hsin, Complex.exp_ofReal_mul_I]

theorem dyadicNode_eq_cos (s j : ℕ) :
    dyadicNode s j = Real.cos (((2*j+1 : ℕ) : ℝ)*Real.pi / (2*(2:ℝ)^s)) := by
  rw [dyadicNode, dyadicRoot_eq_exp, ← Complex.exp_nat_mul]
  have harg : ((2*j+1 : ℕ) : ℂ)*
      (((Real.pi/(2:ℝ)^(s+1) : ℝ) : ℂ)*Complex.I) =
      (((((2*j+1 : ℕ) : ℝ)*Real.pi/(2*(2:ℝ)^s)) : ℝ) : ℂ)*Complex.I := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [harg, Complex.exp_ofReal_mul_I_re]

theorem dyadicNode_mem_interval (s j : ℕ) : dyadicNode s j ∈ Set.Icc (-1:ℝ) 1 := by
  rw [dyadicNode_eq_cos]
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem dyadicNode_injective (s : ℕ) :
    Function.Injective (fun j : Fin (2^s) => dyadicNode s j) := by
  have hangle (j : Fin (2^s)) :
      (((2*j.val+1 : ℕ) : ℝ)*Real.pi/(2*(2:ℝ)^s)) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*2^s)).mpr
      have hj : (j.val : ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast Nat.succ_le_of_lt j.isLt
      have hm := mul_le_mul_of_nonneg_right hj Real.pi_pos.le
      push_cast
      nlinarith [Real.pi_pos]
  intro i j hij
  change dyadicNode s i = dyadicNode s j at hij
  rw [dyadicNode_eq_cos, dyadicNode_eq_cos] at hij
  have hargs := Real.strictAntiOn_cos.injOn (hangle i) (hangle j) hij
  have hmul := (div_left_inj' (by positivity : (2*(2:ℝ)^s) ≠ 0)).mp hargs
  have hcoeff := mul_right_cancel₀ Real.pi_ne_zero hmul
  apply Fin.ext
  have heq : (i.val : ℝ) = (j.val : ℝ) := by push_cast at hcoeff; linarith
  exact_mod_cast heq

def inverseRootValue (η x : ℝ) : ℝ :=
  (Real.sqrt (Real.sqrt (x^2+η^2)+η))⁻¹

def inverseRootInterpolant (s : ℕ) (η : ℝ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j)
    (fun j => inverseRootValue η (dyadicNode s j))

theorem inverseRootInterpolant_at_node (s : ℕ) (η : ℝ) (j : Fin (2^s)) :
    (inverseRootInterpolant s η).eval (dyadicNode s j) = inverseRootValue η (dyadicNode s j) := by
  unfold inverseRootInterpolant
  exact Lagrange.eval_interpolate_at_node _ (dyadicNode_injective s).injOn (Finset.mem_univ j)

theorem inverseRootInterpolant_degree (s : ℕ) (η : ℝ) :
    (inverseRootInterpolant s η).degree < (2^s : ℕ) := by
  simpa [inverseRootInterpolant] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (v := fun j : Fin (2^s) => dyadicNode s j.val)
      (r := fun j : Fin (2^s) => inverseRootValue η (dyadicNode s j.val))
      (dyadicNode_injective s).injOn

theorem inverseRootValue_exact (η x : ℝ) (hη : 0 < η) :
    inverseRootValue η x * Real.sqrt (absoluteRootScalar η x) = 1 := by
  unfold inverseRootValue absoluteRootScalar
  apply inv_mul_cancel₀
  have hf := scalar_absolute_root_pos η x hη
  exact (Real.sqrt_pos.mpr hf).ne'

end
end HierarchicalAbsoluteSpectral
