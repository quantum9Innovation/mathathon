import PairModes
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Matrix
open scoped BigOperators

namespace CriticalPairs

noncomputable section

def squaredNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

def euclideanNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (squaredNorm v)

def removedCoupling (q p : ℕ) (b : ℝ) :
    Matrix (Option (Fin q) ⊕ (Fin p × Bool)) (Option (Fin q) ⊕ (Fin p × Bool)) ℝ :=
  fun i j => match i, j with
    | Sum.inl none, Sum.inr _ => b
    | Sum.inr _, Sum.inl none => b
    | _, _ => 0

def coupled (q p : ℕ) (b : ℝ) (w : Fin p → ℝ) :=
  decoupled q p b w + removedCoupling q p b

def restrictedCoupling (q p : ℕ) (b : ℝ) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => b)

theorem removedCoupling_host (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    (removedCoupling q p b *ᵥ v) (Sum.inl none) =
      b * ∑ j : Fin p × Bool, v (Sum.inr j) := by
  simp [Matrix.mulVec, dotProduct, removedCoupling, Fintype.sum_sum_type,
    Finset.mul_sum]

theorem removedCoupling_free (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) (i : Fin q) :
    (removedCoupling q p b *ᵥ v) (Sum.inl (some i)) = 0 := by
  simp [Matrix.mulVec, dotProduct, removedCoupling]

theorem removedCoupling_pair (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) (i : Fin p × Bool) :
    (removedCoupling q p b *ᵥ v) (Sum.inr i) = b * v (Sum.inl none) := by
  simp [Matrix.mulVec, dotProduct, removedCoupling, Fintype.sum_sum_type]

theorem restrictedCoupling_squaredNorm (q p : ℕ) (b : ℝ) :
    squaredNorm (restrictedCoupling q p b) = (2 * p : ℝ) * b ^ 2 := by
  simp [squaredNorm, restrictedCoupling, Fintype.sum_sum_type, mul_comm]

theorem squaredNorm_split (q p : ℕ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    squaredNorm v = v (Sum.inl none) ^ 2 +
      (∑ i : Fin q, v (Sum.inl (some i)) ^ 2) +
      ∑ i : Fin p × Bool, v (Sum.inr i) ^ 2 := by
  simp [squaredNorm, Fintype.sum_sum_type]

theorem removedCoupling_squaredNorm (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    squaredNorm (removedCoupling q p b *ᵥ v) =
      (b * ∑ i : Fin p × Bool, v (Sum.inr i)) ^ 2 +
      (2 * p : ℝ) * (b * v (Sum.inl none)) ^ 2 := by
  rw [squaredNorm_split]
  simp [removedCoupling_host, removedCoupling_free, removedCoupling_pair,
    Fintype.sum_prod_type, mul_comm]

theorem pair_sum_square_bound (p : ℕ) (v : Fin p × Bool → ℝ) :
    (∑ i, v i) ^ 2 ≤ (2 * p : ℝ) * ∑ i, v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p × Bool))
    (fun _ => (1 : ℝ)) v
  simpa [Fintype.card_prod, mul_comm] using h

theorem removedCoupling_squaredNorm_bound (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    squaredNorm (removedCoupling q p b *ᵥ v) ≤
      ((2 * p : ℝ) * b ^ 2) * squaredNorm v := by
  rw [removedCoupling_squaredNorm, squaredNorm_split]
  have hs := mul_le_mul_of_nonneg_left (pair_sum_square_bound p (v ∘ Sum.inr))
    (sq_nonneg b)
  have hfree : 0 ≤ ∑ i : Fin q, v (Sum.inl (some i)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoef : 0 ≤ (2 * p : ℝ) * b ^ 2 := by positivity
  have he := mul_nonneg hcoef hfree
  simp only [Function.comp_apply] at hs
  nlinarith

theorem removedCoupling_euclideanNorm_bound (q p : ℕ) (b : ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    euclideanNorm (removedCoupling q p b *ᵥ v) ≤
      (|b| * Real.sqrt (2 * p)) * euclideanNorm v := by
  unfold euclideanNorm
  have h := Real.sqrt_le_sqrt (removedCoupling_squaredNorm_bound q p b v)
  have hn : 0 ≤ (2 * p : ℝ) := by positivity
  have hc : 0 ≤ (2 * p : ℝ) * b ^ 2 := by positivity
  rw [Real.sqrt_mul hc, Real.sqrt_mul hn, Real.sqrt_sq_eq_abs] at h
  simpa [mul_comm] using h

theorem coupled_difference_bound (q p : ℕ) (b : ℝ) (w : Fin p → ℝ)
    (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ) :
    euclideanNorm ((coupled q p b w - decoupled q p b w) *ᵥ v) ≤
      (|b| * Real.sqrt (2 * p)) * euclideanNorm v := by
  simpa [coupled] using removedCoupling_euclideanNorm_bound q p b v

#print axioms removedCoupling_host
#print axioms removedCoupling_free
#print axioms removedCoupling_pair
#print axioms restrictedCoupling_squaredNorm
#print axioms squaredNorm_split
#print axioms removedCoupling_squaredNorm
#print axioms pair_sum_square_bound
#print axioms removedCoupling_squaredNorm_bound
#print axioms removedCoupling_euclideanNorm_bound
#print axioms coupled_difference_bound

end

end CriticalPairs
