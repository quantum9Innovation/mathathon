import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

namespace GrowingDefects

open Matrix

theorem projected_resolvent_polynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P R : Matrix ι ι ℝ) (z d : ℝ)
    (hL : (z • (1 : Matrix ι ι ℝ) - A) * R = 1 - P)
    (hR : R * (z • (1 : Matrix ι ι ℝ) - A) = 1 - P)
    (hPA : P * A = d • P) :
    A * R * A = z ^ 2 • R - z • (1 : Matrix ι ι ℝ) - A + (z + d) • P := by
  have hAR : A * R = z • R - 1 + P := by
    simp only [sub_mul, smul_mul, one_mul] at hL
    calc
      A * R = z • R - (z • R - A * R) := by module
      _ = z • R - (1 - P) := by rw [hL]
      _ = z • R - 1 + P := by module
  have hRA : R * A = z • R - 1 + P := by
    simp only [mul_sub, Matrix.mul_smul, mul_one] at hR
    calc
      R * A = z • R - (z • R - R * A) := by module
      _ = z • R - (1 - P) := by rw [hR]
      _ = z • R - 1 + P := by module
  rw [hAR, add_mul, sub_mul, smul_mul, one_mul, hRA, hPA]
  module

theorem marked_schur_identity
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A P R : Matrix ι ι ℝ) (E : Matrix ι κ ℝ) (z d : ℝ)
    (hL : (z • (1 : Matrix ι ι ℝ) - A) * R = 1 - P)
    (hR : R * (z • (1 : Matrix ι ι ℝ) - A) = 1 - P)
    (hPA : P * A = d • P) (hE : E.transpose * E = 1) :
    z • (1 : Matrix κ κ ℝ) - E.transpose * (A * R * A) * E =
      (2 * z) • (1 : Matrix κ κ ℝ) - z ^ 2 • (E.transpose * R * E) +
        E.transpose * A * E - (z + d) • (E.transpose * P * E) := by
  rw [projected_resolvent_polynomial A P R z d hL hR hPA]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hE]
  module

def selectionMatrix {n m : ℕ} (c : Fin m ↪ Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => if i = c j then 1 else 0

theorem selection_isometry {n m : ℕ} (c : Fin m ↪ Fin n) :
    (selectionMatrix c).transpose * selectionMatrix c = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, selectionMatrix,
    mul_ite, c.injective.eq_iff, Matrix.one_apply, eq_comm]

noncomputable def stationaryMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => 1 / (n : ℝ)

noncomputable def markedStationary (n m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun _ _ => 1 / (n : ℝ)

theorem marked_stationary_matrix {n m : ℕ} (c : Fin m ↪ Fin n) :
    (selectionMatrix c).transpose * stationaryMatrix n * selectionMatrix c =
      markedStationary n m := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, selectionMatrix, stationaryMatrix, markedStationary,
    ite_mul, mul_ite]

theorem stationary_mul_of_column_sum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (d : ℝ) (hcol : ∀ j, ∑ i, A i j = d) :
    stationaryMatrix n * A = d • stationaryMatrix n := by
  ext i j
  simp [Matrix.mul_apply, stationaryMatrix, ← Finset.sum_mul, hcol, mul_comm]

theorem actual_marked_schur_identity {n m : ℕ} (c : Fin m ↪ Fin n)
    (A R : Matrix (Fin n) (Fin n) ℝ) (z d : ℝ)
    (hL : (z • (1 : Matrix (Fin n) (Fin n) ℝ) - A) * R = 1 - stationaryMatrix n)
    (hR : R * (z • (1 : Matrix (Fin n) (Fin n) ℝ) - A) = 1 - stationaryMatrix n)
    (hcol : ∀ j, ∑ i, A i j = d) :
    z • (1 : Matrix (Fin m) (Fin m) ℝ) -
        (selectionMatrix c).transpose * (A * R * A) * selectionMatrix c =
      (2 * z) • (1 : Matrix (Fin m) (Fin m) ℝ) -
        z ^ 2 • ((selectionMatrix c).transpose * R * selectionMatrix c) +
        (selectionMatrix c).transpose * A * selectionMatrix c -
        (z + d) • markedStationary n m := by
  have h := marked_schur_identity A (stationaryMatrix n) R (selectionMatrix c)
    z d hL hR (stationary_mul_of_column_sum n A d hcol) (selection_isometry c)
  simpa only [marked_stationary_matrix] using h

#print axioms projected_resolvent_polynomial
#print axioms marked_schur_identity
#print axioms selection_isometry
#print axioms marked_stationary_matrix
#print axioms stationary_mul_of_column_sum
#print axioms actual_marked_schur_identity

end GrowingDefects
