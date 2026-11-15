import AggregateBlock

open Matrix CriticalPairs
open scoped BigOperators

namespace CriticalSubspaces

noncomputable section

def collectiveBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0],
    ![1 / Real.sqrt 2, -1 / Real.sqrt 2, 0],
    ![0, 0, 1]]

def splitBrightMatrix (α β w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![α, 0, β / Real.sqrt 2],
    ![0, -α, β / Real.sqrt 2],
    ![β / Real.sqrt 2, β / Real.sqrt 2, w]]

theorem collectiveBasis_orthogonal :
    collectiveBasis.transpose * collectiveBasis = 1 := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [collectiveBasis, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp
  all_goals nlinarith

theorem collectiveBasis_intertwines (α β w : ℝ) :
    brightMatrix α β w * collectiveBasis = collectiveBasis * splitBrightMatrix α β w := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [collectiveBasis, brightMatrix, splitBrightMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ]
  all_goals field_simp
  all_goals nlinarith [congrArg (fun r : ℝ => β * r) hs2]

theorem normalized_bright_characteristic (q p : ℕ) (hq : 0 < q) (κ w z : ℝ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      brightMatrix ((κ / Real.sqrt (q + 2 * p)) * Real.sqrt q)
        ((κ / Real.sqrt (q + 2 * p)) * Real.sqrt (2 * p)) w).det =
      (z - w) * (z ^ 2 - κ ^ 2) - (2 * κ ^ 2 * p * w) / (q + 2 * p) := by
  have hm : (q : ℝ) + 2 * p ≠ 0 := by positivity
  rw [brightMatrix_characteristic]
  simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg q),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 * p by positivity),
    Real.sq_sqrt (show (0 : ℝ) ≤ q + 2 * p by positivity)]
  field_simp
  ring

def twoLevelMatrix (a τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, a], ![a, τ]]

def twoLevelRoot (a τ σ : ℝ) : ℝ :=
  (τ + σ * Real.sqrt (τ ^ 2 + 4 * a ^ 2)) / 2

def twoLevelVector (a τ σ : ℝ) : Fin 2 → ℝ :=
  ![a, twoLevelRoot a τ σ]

theorem twoLevel_characteristic (a τ z : ℝ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℝ) - twoLevelMatrix a τ).det =
      z ^ 2 - τ * z - a ^ 2 := by
  simp [Matrix.det_fin_two, twoLevelMatrix, Matrix.sub_apply]
  ring

theorem twoLevelRoot_equation (a τ σ : ℝ) (hσ : σ ^ 2 = 1) :
    twoLevelRoot a τ σ ^ 2 = τ * twoLevelRoot a τ σ + a ^ 2 := by
  have hΔ : 0 ≤ τ ^ 2 + 4 * a ^ 2 := by positivity
  have hs : (σ * Real.sqrt (τ ^ 2 + 4 * a ^ 2)) ^ 2 = τ ^ 2 + 4 * a ^ 2 := by
    rw [mul_pow, hσ, one_mul, Real.sq_sqrt hΔ]
  unfold twoLevelRoot
  nlinarith

theorem twoLevelRoot_hasEigenvector (a τ σ : ℝ) (ha : a ≠ 0) (hσ : σ ^ 2 = 1) :
    Module.End.HasEigenvector (twoLevelMatrix a τ).mulVecLin (twoLevelRoot a τ σ)
      (twoLevelVector a τ σ) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · change twoLevelMatrix a τ *ᵥ twoLevelVector a τ σ =
      twoLevelRoot a τ σ • twoLevelVector a τ σ
    have he := twoLevelRoot_equation a τ σ hσ
    ext i
    fin_cases i
    · simp [twoLevelMatrix, twoLevelVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        mul_comm]
    · simp [twoLevelMatrix, twoLevelVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      nlinarith
  · intro h
    have h0 := congrFun h 0
    simp [twoLevelVector] at h0
    exact ha h0

theorem twoLevelRoots_distinct (a τ : ℝ) (ha : a ≠ 0) :
    twoLevelRoot a τ 1 ≠ twoLevelRoot a τ (-1) := by
  have hΔ : 0 < τ ^ 2 + 4 * a ^ 2 := by
    nlinarith [sq_nonneg τ, sq_pos_of_ne_zero ha]
  have hs := Real.sqrt_pos.mpr hΔ
  unfold twoLevelRoot
  intro h
  nlinarith

theorem twoLevel_resonant_masses (a σ : ℝ) (ha : a ≠ 0) (hσ : σ ^ 2 = 1) :
    (twoLevelVector a 0 σ 0) ^ 2 / squaredNorm (twoLevelVector a 0 σ) = 1 / 2 ∧
    (twoLevelVector a 0 σ 1) ^ 2 / squaredNorm (twoLevelVector a 0 σ) = 1 / 2 := by
  have he : twoLevelRoot a 0 σ ^ 2 = a ^ 2 := by
    simpa using twoLevelRoot_equation a 0 σ hσ
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hn : squaredNorm (twoLevelVector a 0 σ) = a ^ 2 + twoLevelRoot a 0 σ ^ 2 := by
    simp [squaredNorm, twoLevelVector, Fin.sum_univ_succ]
  change a ^ 2 / squaredNorm (twoLevelVector a 0 σ) = 1 / 2 ∧
    twoLevelRoot a 0 σ ^ 2 / squaredNorm (twoLevelVector a 0 σ) = 1 / 2
  rw [hn, he]
  constructor
  · field_simp
    norm_num
  · field_simp
    norm_num

#print axioms collectiveBasis_orthogonal
#print axioms collectiveBasis_intertwines
#print axioms normalized_bright_characteristic
#print axioms twoLevel_characteristic
#print axioms twoLevelRoot_equation
#print axioms twoLevelRoot_hasEigenvector
#print axioms twoLevelRoots_distinct
#print axioms twoLevel_resonant_masses

end

end CriticalSubspaces
