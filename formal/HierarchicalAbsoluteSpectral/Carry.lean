import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.NoncommRing

/-!
Section 6, equations (15)--(16): the carried-preimage identity.
All matrices are real. No commutation or symmetry assumption is made on
successive factors. Inverses below are ordinary nonsingular matrix inverses.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section

open Matrix Polynomial

variable {k r n : ℕ}

def filteredOperator (A₀ S : Matrix (Fin k) (Fin k) ℝ) :=
  1 - Sᵀ * A₀ * S

def carriedOperator (A₀ S : Matrix (Fin k) (Fin k) ℝ) :=
  1 - A₀ * S * Sᵀ

/-- The exact intertwining identity `T Sᵀ = Sᵀ V₀`. -/
theorem carried_intertwining (A₀ S : Matrix (Fin k) (Fin k) ℝ) :
    filteredOperator A₀ S * Sᵀ = Sᵀ * carriedOperator A₀ S := by
  unfold filteredOperator carriedOperator
  noncomm_ring

/-- Intertwining passes through every finite real polynomial. -/
theorem polynomial_intertwining
    (T V J : Matrix (Fin k) (Fin k) ℝ) (h : T * J = J * V) (p : ℝ[X]) :
    aeval T p * J = J * aeval V p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial i c =>
    have hpow : T^i * J = J * V^i := by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ', mul_assoc, ih, ← mul_assoc T, h, mul_assoc, ← pow_succ']
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, mul_smul_comm, hpow]

/-- First two identities in equation (16), for the actual rectangular Gaussian block. -/
theorem carried_filter_identity
    (A₀ S : Matrix (Fin k) (Fin k) ℝ) (p : ℝ[X])
    (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    aeval (filteredOperator A₀ S) p * (Sᵀ * Ξ) =
      Sᵀ * (aeval (carriedOperator A₀ S) p * Ξ) := by
  rw [← Matrix.mul_assoc, polynomial_intertwining _ _ _ (carried_intertwining A₀ S),
    Matrix.mul_assoc]

/-- The last identity in (16): compute the physical lift without a fine inverse. -/
theorem exact_carried_preimage
    (R₀ S A₀ : Matrix (Fin k) (Fin k) ℝ)
    (hS : IsUnit S.det) (p : ℝ[X]) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    ((R₀ * S)⁻¹)ᵀ *
        (aeval (filteredOperator A₀ S) p * (Sᵀ * Ξ)) =
      (R₀⁻¹)ᵀ * (aeval (carriedOperator A₀ S) p * Ξ) := by
  rw [carried_filter_identity, Matrix.mul_inv_rev, transpose_mul]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (R₀⁻¹)ᵀ, ← transpose_mul,
    Matrix.mul_nonsing_inv _ hS, transpose_one, mul_one]

/-- The executable physical span is exactly the dual lift in Lemma 6. -/
theorem exact_physical_lift
    (Z : Matrix (Fin n) (Fin k) ℝ)
    (R₀ S A₀ : Matrix (Fin k) (Fin k) ℝ)
    (hS : IsUnit S.det) (p : ℝ[X]) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    Z * (((R₀ * S)⁻¹)ᵀ *
        (aeval (filteredOperator A₀ S) p * (Sᵀ * Ξ))) =
      Z * ((R₀⁻¹)ᵀ * (aeval (carriedOperator A₀ S) p * Ξ)) := by
  rw [exact_carried_preimage R₀ S A₀ hS p Ξ]

/-- A width-`r` output has rank at most `r`, including dependent columns. -/
theorem output_rank_le (U : Matrix (Fin n) (Fin r) ℝ)
    (V : Matrix (Fin r) (Fin k) ℝ) : (U * V).rank ≤ r :=
  (Matrix.rank_mul_le_left U V).trans U.rank_le_width

end
end HierarchicalAbsoluteSpectral
