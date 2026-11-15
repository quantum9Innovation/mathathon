import ProjectedResolvent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp

namespace GrowingDefects

open Matrix

noncomputable section

def regularizedMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) : Matrix ι ι ℝ :=
  d • (1 : Matrix ι ι ℝ) - A + P

def constructedProjectedInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)] :
    Matrix ι ι ℝ :=
  ⅟(regularizedMatrix A P d) - P

theorem regularized_mul_projector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) (hAP : A * P = d • P) (hPP : P * P = P) :
    regularizedMatrix A P d * P = P := by
  simp [regularizedMatrix, Matrix.add_mul, Matrix.sub_mul, hAP, hPP]

theorem projector_mul_regularized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) (hPA : P * A = d • P) (hPP : P * P = P) :
    P * regularizedMatrix A P d = P := by
  simp [regularizedMatrix, Matrix.mul_add, Matrix.mul_sub, hPA, hPP]

theorem regularized_inverse_mul_projector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)]
    (hAP : A * P = d • P) (hPP : P * P = P) :
    ⅟(regularizedMatrix A P d) * P = P := by
  calc
    ⅟(regularizedMatrix A P d) * P =
        ⅟(regularizedMatrix A P d) * (regularizedMatrix A P d * P) := by
      rw [regularized_mul_projector A P d hAP hPP]
    _ = P := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

theorem projector_mul_regularized_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)]
    (hPA : P * A = d • P) (hPP : P * P = P) :
    P * ⅟(regularizedMatrix A P d) = P := by
  calc
    P * ⅟(regularizedMatrix A P d) =
        (P * regularizedMatrix A P d) * ⅟(regularizedMatrix A P d) := by
      rw [projector_mul_regularized A P d hPA hPP]
    _ = P := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

theorem constructed_projected_inverse_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)]
    (hAP : A * P = d • P) (hPA : P * A = d • P) (hPP : P * P = P) :
    (d • (1 : Matrix ι ι ℝ) - A) * constructedProjectedInverse A P d = 1 - P := by
  have hbase : d • (1 : Matrix ι ι ℝ) - A = regularizedMatrix A P d - P := by
    simp [regularizedMatrix]
  rw [hbase, constructedProjectedInverse]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, mul_invOf_self,
    regularized_mul_projector A P d hAP hPP,
    projector_mul_regularized_inverse A P d hPA hPP, hPP]
  module

theorem constructed_projected_inverse_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)]
    (hAP : A * P = d • P) (hPA : P * A = d • P) (hPP : P * P = P) :
    constructedProjectedInverse A P d * (d • (1 : Matrix ι ι ℝ) - A) = 1 - P := by
  have hbase : d • (1 : Matrix ι ι ℝ) - A = regularizedMatrix A P d - P := by
    simp [regularizedMatrix]
  rw [hbase, constructedProjectedInverse]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, invOf_mul_self,
    regularized_inverse_mul_projector A P d hAP hPP,
    projector_mul_regularized A P d hPA hPP, hPP]
  module

theorem constructed_projected_inverse_centered
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (d : ℝ) [Invertible (regularizedMatrix A P d)]
    (hAP : A * P = d • P) (hPA : P * A = d • P) (hPP : P * P = P) :
    P * constructedProjectedInverse A P d = 0 ∧
      constructedProjectedInverse A P d * P = 0 := by
  constructor
  · simp only [constructedProjectedInverse, Matrix.mul_sub,
      projector_mul_regularized_inverse A P d hPA hPP, hPP, sub_self]
  · simp only [constructedProjectedInverse, Matrix.sub_mul,
      regularized_inverse_mul_projector A P d hAP hPP, hPP, sub_self]

theorem stationary_idempotent (n : ℕ) (hn : 0 < n) :
    stationaryMatrix n * stationaryMatrix n = stationaryMatrix n := by
  apply (stationary_mul_of_column_sum n (stationaryMatrix n) 1 ?_).trans
  · exact one_smul ℝ (stationaryMatrix n)
  · intro j
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    simp [stationaryMatrix, hn']

theorem mul_stationary_of_row_sum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (d : ℝ) (hrow : ∀ i, ∑ j, A i j = d) :
    A * stationaryMatrix n = d • stationaryMatrix n := by
  ext i j
  simp only [Matrix.mul_apply, stationaryMatrix, Matrix.smul_apply]
  rw [← Finset.sum_mul, hrow]
  rfl

theorem actual_constructed_marked_identity {n m : ℕ} (hn : 0 < n)
    (c : Fin m ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℝ) (d : ℝ)
    [Invertible (regularizedMatrix A (stationaryMatrix n) d)]
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d) :
    d • (1 : Matrix (Fin m) (Fin m) ℝ) -
        (selectionMatrix c).transpose *
          (A * constructedProjectedInverse A (stationaryMatrix n) d * A) * selectionMatrix c =
      (2 * d) • (1 : Matrix (Fin m) (Fin m) ℝ) -
        d ^ 2 • ((selectionMatrix c).transpose *
          constructedProjectedInverse A (stationaryMatrix n) d * selectionMatrix c) +
        (selectionMatrix c).transpose * A * selectionMatrix c -
        (d + d) • markedStationary n m := by
  have hAP := mul_stationary_of_row_sum n A d hrow
  have hPA := stationary_mul_of_column_sum n A d hcol
  have hPP := stationary_idempotent n hn
  exact actual_marked_schur_identity c A (constructedProjectedInverse A (stationaryMatrix n) d)
    d d (constructed_projected_inverse_left A (stationaryMatrix n) d hAP hPA hPP)
    (constructed_projected_inverse_right A (stationaryMatrix n) d hAP hPA hPP) hcol

#print axioms regularized_mul_projector
#print axioms projector_mul_regularized
#print axioms regularized_inverse_mul_projector
#print axioms projector_mul_regularized_inverse
#print axioms constructed_projected_inverse_left
#print axioms constructed_projected_inverse_right
#print axioms constructed_projected_inverse_centered
#print axioms stationary_idempotent
#print axioms mul_stationary_of_row_sum
#print axioms actual_constructed_marked_identity

end

end GrowingDefects
