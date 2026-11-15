import CouplingError

open Matrix
open scoped BigOperators

namespace CriticalPairs

noncomputable section

def normalizedDecoupled (q p : ℕ) (κ : ℝ) (w : Fin p → ℝ) :=
  decoupled q p (κ / Real.sqrt (q + 2 * p)) w

def normalizedCoupled (q p : ℕ) (κ : ℝ) (w : Fin p → ℝ) :=
  coupled q p (κ / Real.sqrt (q + 2 * p)) w

theorem normalized_collective_coefficient (q p : ℕ) (κ : ℝ) :
    (κ / Real.sqrt (q + 2 * p)) * Real.sqrt q =
      κ * Real.sqrt ((q : ℝ) / (q + 2 * p)) := by
  rw [Real.sqrt_div (Nat.cast_nonneg q)]
  ring

theorem normalized_eigenvalue_coverage (q p : ℕ) (κ μ : ℝ) (w : Fin p → ℝ)
    (he : Module.End.HasEigenvalue (normalizedDecoupled q p κ w).mulVecLin μ) :
    μ = 0 ∨ μ = κ * Real.sqrt ((q : ℝ) / (q + 2 * p)) ∨
      μ = -(κ * Real.sqrt ((q : ℝ) / (q + 2 * p))) ∨
      ∃ k : Fin p, μ = w k ∨ μ = -w k := by
  simpa only [normalized_collective_coefficient] using
    decoupled_eigenvalue_coverage q p (κ / Real.sqrt (q + 2 * p)) μ w he

theorem normalized_bright_hasEigenvector (q p : ℕ) (hq : 0 < q)
    (κ σ : ℝ) (w : Fin p → ℝ) (hσ : σ ^ 2 = 1) :
    Module.End.HasEigenvector (normalizedDecoupled q p κ w).mulVecLin
      (σ * (κ * Real.sqrt ((q : ℝ) / (q + 2 * p))))
      (embeddedBright q p (σ * Real.sqrt q)) := by
  have ht : (σ * Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := by
    rw [mul_pow, hσ, Real.sq_sqrt (Nat.cast_nonneg q), one_mul]
  have h := decoupled_bright_hasEigenvector q p hq (κ / Real.sqrt (q + 2 * p))
    w (σ * Real.sqrt q) ht
  have hc : (κ / Real.sqrt (q + 2 * p)) * (σ * Real.sqrt q) =
      σ * (κ * Real.sqrt ((q : ℝ) / (q + 2 * p))) := by
    rw [← normalized_collective_coefficient]
    ring
  simpa only [normalizedDecoupled, hc] using h

theorem normalized_pair_hasEigenvector (q p : ℕ) (κ : ℝ) (w : Fin p → ℝ)
    (k : Fin p) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    Module.End.HasEigenvector (normalizedDecoupled q p κ w).mulVecLin
      (σ * w k) (embeddedPair q p k σ) :=
  decoupled_pair_hasEigenvector q p (κ / Real.sqrt (q + 2 * p)) w k σ hσ

theorem normalized_restrictedCoupling_squaredNorm (q p : ℕ) (κ : ℝ) :
    squaredNorm (restrictedCoupling q p (κ / Real.sqrt (q + 2 * p))) =
      κ ^ 2 * ((2 * p : ℝ) / (q + 2 * p)) := by
  rw [restrictedCoupling_squaredNorm, div_pow, Real.sq_sqrt (by positivity)]
  ring

theorem normalized_error_coefficient (q p : ℕ) (κ : ℝ) :
    |κ / Real.sqrt (q + 2 * p)| * Real.sqrt (2 * p) =
      |κ| * Real.sqrt ((2 * p : ℝ) / (q + 2 * p)) := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_div (by positivity)]
  ring

theorem normalized_decoupling_bound (q p : ℕ) (κ : ℝ) (w : Fin p → ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    euclideanNorm ((normalizedCoupled q p κ w - normalizedDecoupled q p κ w) *ᵥ v) ≤
      (|κ| * Real.sqrt ((2 * p : ℝ) / (q + 2 * p))) * euclideanNorm v := by
  simpa only [normalizedCoupled, normalizedDecoupled, normalized_error_coefficient] using
    coupled_difference_bound q p (κ / Real.sqrt (q + 2 * p)) w v

#print axioms normalized_collective_coefficient
#print axioms normalized_eigenvalue_coverage
#print axioms normalized_bright_hasEigenvector
#print axioms normalized_pair_hasEigenvector
#print axioms normalized_restrictedCoupling_squaredNorm
#print axioms normalized_error_coefficient
#print axioms normalized_decoupling_bound

end

end CriticalPairs
