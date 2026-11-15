import PortEnergy
import Mathlib.Tactic.NormNum

namespace StructuralDefects

open Matrix

noncomputable section

def starSeven : Matrix (Option (Fin 7)) (Option (Fin 7)) ℝ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some _, some _ => 0

def starSevenShift : Matrix (Option (Fin 7)) (Option (Fin 7)) ℝ :=
  (3 : ℝ) • 1 - starSeven

def starSevenInverse : Matrix (Option (Fin 7)) (Option (Fin 7)) ℝ
  | none, none => 3 / 2
  | none, some _ => 1 / 2
  | some _, none => 1 / 2
  | some i, some j => (if i = j then 1 / 3 else 0) + 1 / 6

def starSevenPort : Option (Fin 7) → ℝ := Pi.single none 1

theorem starSeven_symmetric : starSeven.transpose = starSeven := by
  ext i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => rfl
  | some i =>
    cases j with
    | none => rfl
    | some j => rfl

theorem starSevenInverse_symmetric : starSevenInverse.transpose = starSevenInverse := by
  ext i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => rfl
  | some i =>
    cases j with
    | none => rfl
    | some j => simp [Matrix.transpose_apply, starSevenInverse, eq_comm]

theorem starSeven_inverse_right : starSevenShift * starSevenInverse = 1 := by
  have hnone : ∀ j : Fin 7, (none : Option (Fin 7)) ≠ some j := by
    intro j h
    cases h
  ext i j
  cases i with
  | none =>
    cases j with
    | none => norm_num [Matrix.mul_apply, Fintype.sum_option, starSevenShift,
        starSeven, starSevenInverse, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        hnone]
    | some j => norm_num [Matrix.mul_apply, Fintype.sum_option, starSevenShift,
        starSeven, starSevenInverse, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Finset.sum_add_distrib, ite_mul, hnone]
  | some i =>
    cases j with
    | none => norm_num [Matrix.mul_apply, Fintype.sum_option, starSevenShift,
        starSeven, starSevenInverse, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        ite_mul, Option.some_ne_none]
    | some j =>
      by_cases hij : i = j
      · subst j
        norm_num [Matrix.mul_apply, Fintype.sum_option, starSevenShift,
          starSeven, starSevenInverse, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          ite_mul, mul_ite, Option.some_ne_none]
      · norm_num [Matrix.mul_apply, Fintype.sum_option, starSevenShift,
          starSeven, starSevenInverse, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          ite_mul, mul_ite, hij, Ne.symm hij, Option.some_ne_none]

theorem starSeven_inverse_left : starSevenInverse * starSevenShift = 1 := by
  have h := congrArg Matrix.transpose starSeven_inverse_right
  simpa only [Matrix.transpose_mul, Matrix.transpose_one, starSevenInverse_symmetric,
    starSevenShift, Matrix.transpose_sub, Matrix.transpose_smul, starSeven_symmetric] using h

instance starSevenInvertible : Invertible starSevenShift where
  invOf := starSevenInverse
  invOf_mul_self := starSeven_inverse_left
  mul_invOf_self := starSeven_inverse_right

theorem starSeven_invOf : ⅟starSevenShift = starSevenInverse := rfl

theorem starSeven_response : portResponse starSevenShift starSevenPort = 3 / 2 := by
  norm_num [portResponse, starSevenPort, starSeven_invOf, starSevenInverse]

theorem starSeven_profile : portProfile starSevenShift starSevenPort =
    fun i => match i with
      | none => 1
      | some _ => 1 / 3 := by
  unfold portProfile
  rw [starSeven_response]
  funext i
  cases i with
  | none => norm_num [starSevenPort,
      starSeven_invOf, starSevenInverse]
  | some i => norm_num [starSevenPort,
      starSeven_invOf, starSevenInverse]

theorem starSeven_profile_gram :
    portProfile starSevenShift starSevenPort ⬝ᵥ portProfile starSevenShift starSevenPort =
      16 / 9 := by
  rw [starSeven_profile]
  norm_num [dotProduct, Fintype.sum_option]

theorem starSeven_port_energy (y : Option (Fin 7) → ℝ) :
    y ⬝ᵥ (starSevenShift *ᵥ y) =
      (2 / 3) * (y none) ^ 2 +
      portRemainder starSevenShift starSevenPort y ⬝ᵥ
        (starSevenShift *ᵥ portRemainder starSevenShift starSevenPort y) := by
  have hs : starSevenShift.transpose = starSevenShift := by
    simp only [starSevenShift, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, starSeven_symmetric]
  have h := actual_port_energy_decomposition starSevenShift hs starSevenPort y
    (by rw [starSeven_response]
        norm_num)
  rw [starSeven_response] at h
  simpa [starSevenPort] using h

#print axioms starSeven_symmetric
#print axioms starSevenInverse_symmetric
#print axioms starSeven_inverse_right
#print axioms starSeven_inverse_left
#print axioms starSeven_invOf
#print axioms starSeven_response
#print axioms starSeven_profile
#print axioms starSeven_profile_gram
#print axioms starSeven_port_energy

end

end StructuralDefects
