import ExactModes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

open Matrix CriticalPairs
open scoped BigOperators

namespace CriticalSubspaces

noncomputable section

def aggregateVector (q p : ℕ) (x : Fin 3 → ℝ) :
    Option (Fin q) ⊕ (Fin p × Bool) → ℝ :=
  Sum.elim (fun i => match i with
    | none => x 0
    | some _ => x 1 / Real.sqrt q) (fun _ => x 2 / Real.sqrt (2 * p))

def aggregateMap (q p : ℕ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Option (Fin q) ⊕ (Fin p × Bool) → ℝ) where
  toFun := aggregateVector q p
  map_add' := by
    intro x y
    funext i
    cases i with
    | inl i =>
      cases i with
      | none => simp [aggregateVector]
      | some i => simp [aggregateVector, add_div]
    | inr i => simp [aggregateVector, add_div]
  map_smul' := by
    intro r x
    funext i
    cases i with
    | inl i =>
      cases i with
      | none => simp [aggregateVector]
      | some i => simp [aggregateVector, mul_div_assoc]
    | inr i => simp [aggregateVector, mul_div_assoc]

def brightMatrix (α β w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, α, β], ![α, 0, 0], ![β, 0, w]]

theorem brightMatrix_action (α β w : ℝ) (x : Fin 3 → ℝ) :
    brightMatrix α β w *ᵥ x = ![α * x 1 + β * x 2, α * x 0, β * x 0 + w * x 2] := by
  ext i
  fin_cases i
  all_goals simp [brightMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem aggregateVector_injective (q p : ℕ) (hq : 0 < q) (hp : 0 < p) :
    Function.Injective (aggregateVector q p) := by
  intro x y h
  have hq0 : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hq)
  have hp0 : Real.sqrt (2 * p : ℝ) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  have hh := congrFun h (Sum.inl none)
  have hf := congrFun h (Sum.inl (some ⟨0, hq⟩))
  have he := congrFun h (Sum.inr (⟨0, hp⟩, false))
  simp only [aggregateVector, Sum.elim_inl, Sum.elim_inr] at hh hf he
  funext i
  fin_cases i
  · exact hh
  · exact (div_left_inj' hq0).mp hf
  · exact (div_left_inj' hp0).mp he

theorem aggregateVector_squaredNorm (q p : ℕ) (hq : 0 < q) (hp : 0 < p)
    (x : Fin 3 → ℝ) :
    squaredNorm (aggregateVector q p x) = squaredNorm x := by
  have hq0 : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hq)
  have hp0 : Real.sqrt (2 * p : ℝ) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  have hq2 := Real.sq_sqrt (Nat.cast_nonneg q)
  have hp2 : Real.sqrt (2 * p : ℝ) ^ 2 = (2 * p : ℝ) := Real.sq_sqrt (by positivity)
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hpr : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  calc
    squaredNorm (aggregateVector q p x) = x 0 ^ 2 +
        (q : ℝ) * (x 1 / Real.sqrt q) ^ 2 +
        (2 * p : ℝ) * (x 2 / Real.sqrt (2 * p)) ^ 2 := by
      rw [squaredNorm_split]
      simp [aggregateVector, mul_comm]
    _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      simp only [div_pow, hq2, hp2]
      field_simp
    _ = squaredNorm x := by
      simp [squaredNorm, Fin.sum_univ_succ, add_assoc]

theorem aggregateVector_intertwines (q p : ℕ) (hq : 0 < q) (hp : 0 < p)
    (b w : ℝ) (x : Fin 3 → ℝ) :
    coupled q p b (fun _ => w) *ᵥ aggregateVector q p x =
      aggregateVector q p (brightMatrix (b * Real.sqrt q) (b * Real.sqrt (2 * p)) w *ᵥ x) := by
  have hq0 : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hq)
  have hp0 : Real.sqrt (2 * p : ℝ) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  have hq2 := Real.sq_sqrt (Nat.cast_nonneg q)
  have hp2 : Real.sqrt (2 * p : ℝ) ^ 2 = (2 * p : ℝ) := Real.sq_sqrt (by positivity)
  rw [brightMatrix_action]
  funext i
  cases i with
  | inl i =>
    cases i with
    | none =>
      simp only [coupled_host, aggregateVector, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod,
        Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
        Matrix.cons_val_zero]
      calc
        b * ((q : ℝ) * (x 1 / Real.sqrt q)) +
            b * ((p : ℝ) * 2 * (x 2 / Real.sqrt (2 * p))) =
          b * ((q : ℝ) / Real.sqrt q) * x 1 +
            b * ((2 * p : ℝ) / Real.sqrt (2 * p)) * x 2 := by ring
        _ = _ := by rw [Real.div_sqrt, Real.div_sqrt]
    | some i =>
      simp [coupled_free, aggregateVector]
      field_simp
  | inr i =>
    rcases i with ⟨k, s⟩
    simp [coupled_pair, aggregateVector]
    field_simp
    all_goals ring

theorem coupled_preserves_aggregate_range (q p : ℕ) (hq : 0 < q) (hp : 0 < p)
    (b w : ℝ) (v : Option (Fin q) ⊕ (Fin p × Bool) → ℝ)
    (hv : v ∈ LinearMap.range (aggregateMap q p)) :
    coupled q p b (fun _ => w) *ᵥ v ∈ LinearMap.range (aggregateMap q p) := by
  obtain ⟨x, rfl⟩ := hv
  refine ⟨brightMatrix (b * Real.sqrt q) (b * Real.sqrt (2 * p)) w *ᵥ x, ?_⟩
  exact (aggregateVector_intertwines q p hq hp b w x).symm

theorem aggregate_eigenvector_lift (q p : ℕ) (hq : 0 < q) (hp : 0 < p)
    (b w μ : ℝ) (x : Fin 3 → ℝ)
    (hx : Module.End.HasEigenvector
      (brightMatrix (b * Real.sqrt q) (b * Real.sqrt (2 * p)) w).mulVecLin μ x) :
    Module.End.HasEigenvector (coupled q p b (fun _ => w)).mulVecLin μ
      (aggregateVector q p x) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · change coupled q p b (fun _ => w) *ᵥ aggregateVector q p x =
      μ • aggregateVector q p x
    rw [aggregateVector_intertwines q p hq hp b w]
    have he := hx.apply_eq_smul
    change brightMatrix (b * Real.sqrt q) (b * Real.sqrt (2 * p)) w *ᵥ x = μ • x at he
    rw [he]
    exact (aggregateMap q p).map_smul μ x
  · intro h
    apply hx.2
    apply aggregateVector_injective q p hq hp
    change (aggregateMap q p) x = (aggregateMap q p) 0
    rw [map_zero]
    exact h

theorem brightMatrix_characteristic (α β w z : ℝ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - brightMatrix α β w).det =
      (z - w) * (z ^ 2 - α ^ 2 - β ^ 2) - β ^ 2 * w := by
  simp [Matrix.det_fin_three, brightMatrix, Matrix.sub_apply]
  ring

#print axioms brightMatrix_action
#print axioms aggregateVector_injective
#print axioms aggregateVector_squaredNorm
#print axioms aggregateVector_intertwines
#print axioms coupled_preserves_aggregate_range
#print axioms aggregate_eigenvector_lift
#print axioms brightMatrix_characteristic

end

end CriticalSubspaces
