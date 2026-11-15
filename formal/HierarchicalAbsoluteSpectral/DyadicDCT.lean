import HierarchicalAbsoluteSpectral.ChebyshevAliasing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss

/-! The exact discrete cosine transform computes the finite interpolant.
This file proves its value formula; its fast implementation is separate. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev Set Finset
open scoped BigOperators

theorem dyadic_quadrature (s : ℕ) (p : ℝ[X]) (hp : p.degree < 2*(2^s : ℕ)) :
    (Real.pi/(2^s : ℕ))*∑ j : Fin (2^s), p.eval (dyadicNode s j) =
      ∫ x, p.eval x ∂measureT := by
  rw [integral_eq_sumZeroes (by positivity : (2^s : ℕ) ≠ 0) hp]
  unfold sumZeroes
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => p.eval (dyadicNode s j)) (2^s)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicNode_eq_cos]
  congr 2
  push_cast
  ring

theorem dyadic_chebyshev_orthogonality (s k l : ℕ) (hk : k < 2^s) (hl : l < 2^s) :
    ∑ j : Fin (2^s), (T ℝ (k : ℤ)).eval (dyadicNode s j) *
      (T ℝ (l : ℤ)).eval (dyadicNode s j) =
      if k = l then (if k = 0 then (2^s : ℝ) else (2^s : ℝ)/2) else 0 := by
  have hn : (2^s : ℝ) ≠ 0 := by positivity
  have hdeg : (T ℝ (k : ℤ) * T ℝ (l : ℤ)).degree < 2*(2^s : ℕ) := by
    rw [degree_mul, degree_T, degree_T, Int.natAbs_natCast, Int.natAbs_natCast]
    exact_mod_cast (show k+l < 2*2^s by omega)
  have hq := dyadic_quadrature s (T ℝ (k : ℤ)*T ℝ (l : ℤ)) hdeg
  simp only [eval_mul, Nat.cast_pow, Nat.cast_ofNat] at hq
  by_cases he : k = l
  · subst l
    rw [if_pos rfl]
    by_cases hk0 : k = 0
    · subst k
      simp
    · rw [integral_T_real_mul_self_measureT_of_ne_zero hk0] at hq
      rw [if_neg hk0]
      apply (mul_left_cancel₀ (show Real.pi/(2^s : ℝ) ≠ 0 by positivity))
      convert hq using 1
      field_simp
  · rw [if_neg he, integral_eval_T_real_mul_eval_T_real_measureT_of_ne he] at *
    exact (mul_eq_zero.mp hq).resolve_left (by positivity)

def dyadicDCTCoefficient (s : ℕ) (v : Fin (2^s) → ℝ) (k : Fin (2^s)) : ℝ :=
  (if k.val = 0 then 1/(2^s : ℝ) else 2/(2^s : ℝ)) *
    ∑ j : Fin (2^s), v j * (T ℝ (k.val : ℤ)).eval (dyadicNode s j)

def dyadicDCT (s : ℕ) : (Fin (2^s) → ℝ) →ₗ[ℝ] ℝ[X] where
  toFun v := ∑ k : Fin (2^s), dyadicDCTCoefficient s v k • T ℝ (k.val : ℤ)
  map_add' v w := by
    have hc (k : Fin (2^s)) : dyadicDCTCoefficient s (v+w) k =
        dyadicDCTCoefficient s v k + dyadicDCTCoefficient s w k := by
      simp only [dyadicDCTCoefficient, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
    simp only [hc, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    have hc (k : Fin (2^s)) : dyadicDCTCoefficient s (r • v) k =
        r*dyadicDCTCoefficient s v k := by
      simp only [dyadicDCTCoefficient, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      ring
    simp only [hc, RingHom.id_apply, Finset.smul_sum, smul_smul]

theorem dyadicDCT_apply (s : ℕ) (v : Fin (2^s) → ℝ) :
    dyadicDCT s v = ∑ k : Fin (2^s), dyadicDCTCoefficient s v k • T ℝ (k.val : ℤ) := rfl

theorem dyadicDCTCoefficient_sampleT (s : ℕ) (k l : Fin (2^s)) :
    dyadicDCTCoefficient s (fun j => (T ℝ (l.val : ℤ)).eval (dyadicNode s j)) k =
      if k = l then 1 else 0 := by
  unfold dyadicDCTCoefficient
  rw [dyadic_chebyshev_orthogonality s l.val k.val l.isLt k.isLt]
  by_cases he : k = l
  · subst l
    simp only [↓reduceIte]
    by_cases hk : k.val = 0 <;> simp [hk]
  · have he' : l.val ≠ k.val := by intro h; apply he; exact Fin.ext h.symm
    simp only [he', ↓reduceIte, mul_zero, he]

theorem dyadicDCT_sampleT (s : ℕ) (l : Fin (2^s)) :
    dyadicDCT s (fun j => (T ℝ (l.val : ℤ)).eval (dyadicNode s j)) = T ℝ (l.val : ℤ) := by
  classical
  simp only [dyadicDCT_apply, dyadicDCTCoefficient_sampleT, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def dyadicSampling (s : ℕ) : ℝ[X] →ₗ[ℝ] (Fin (2^s) → ℝ) :=
  LinearMap.pi (fun j => (aeval (dyadicNode s j)).toLinearMap)

theorem dyadicSampling_apply (s : ℕ) (p : ℝ[X]) (j : Fin (2^s)) :
    dyadicSampling s p j = p.eval (dyadicNode s j) := by
  simp [dyadicSampling, aeval_def]

theorem dyadicDCT_reconstructs_polynomial (s : ℕ) (p : ℝ[X]) (hp : p.degree < (2^s : ℕ)) :
    dyadicDCT s (dyadicSampling s p) = p := by
  let L : ℝ[X] →ₗ[ℝ] ℝ[X] := (dyadicDCT s).comp (dyadicSampling s)
  have hT (l : ℕ) (hl : l < 2^s) : L (T ℝ (l : ℤ)) = T ℝ (l : ℤ) := by
    exact dyadicDCT_sampleT s ⟨l, hl⟩
  have hmem : p ∈ degreeLT ℝ (2^s) := mem_degreeLT.mpr hp
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (2^s) = (Finset.range (2^s) : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  change L _ = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro l hl
  rw [chebyshevTsequence, hT l (Finset.mem_range.mp hl)]

theorem dyadicDCT_eq_interpolant (s : ℕ) (v : Fin (2^s) → ℝ) :
    dyadicDCT s v = Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j) v := by
  let p := Lagrange.interpolate Finset.univ (fun j : Fin (2^s) => dyadicNode s j) v
  have hp : p.degree < (2^s : ℕ) := by
    simpa only [p, Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ)
        (v := fun j : Fin (2^s) => dyadicNode s j) v (dyadicNode_injective s).injOn
  have he : dyadicSampling s p = v := by
    funext j
    rw [dyadicSampling_apply]
    exact Lagrange.eval_interpolate_at_node v (dyadicNode_injective s).injOn (Finset.mem_univ j)
  have hr := dyadicDCT_reconstructs_polynomial s p hp
  rw [he] at hr
  exact hr

theorem inverseRootInterpolant_eq_DCT (s : ℕ) (η : ℝ) :
    inverseRootInterpolant s η = dyadicDCT s (fun j => inverseRootValue η (dyadicNode s j)) :=
  (dyadicDCT_eq_interpolant s _).symm

end
end HierarchicalAbsoluteSpectral
