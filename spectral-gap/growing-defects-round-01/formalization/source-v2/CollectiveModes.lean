import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Matrix

namespace GrowingDefects

noncomputable section

def collectiveMatrix (m : ℕ) (b : ℝ) :
    Matrix (Option (Fin m)) (Option (Fin m)) ℝ :=
  fun i j => match i, j with
    | none, some _ => b
    | some _, none => b
    | _, _ => 0

theorem collectiveMatrix_none (m : ℕ) (b : ℝ)
    (v : Option (Fin m) → ℝ) :
    (collectiveMatrix m b *ᵥ v) none = b * ∑ j : Fin m, v (some j) := by
  simp [Matrix.mulVec, dotProduct, collectiveMatrix, Finset.mul_sum]

theorem collectiveMatrix_some (m : ℕ) (b : ℝ)
    (v : Option (Fin m) → ℝ) (i : Fin m) :
    (collectiveMatrix m b *ᵥ v) (some i) = b * v none := by
  simp [Matrix.mulVec, dotProduct, collectiveMatrix]

def brightVector (m : ℕ) (t : ℝ) : Option (Fin m) → ℝ
  | none => t
  | some _ => 1

theorem brightVector_eigen (m : ℕ) (b t : ℝ) (ht : t ^ 2 = (m : ℝ)) :
    collectiveMatrix m b *ᵥ brightVector m t =
      (b * t) • brightVector m t := by
  funext i
  cases i with
  | none =>
    simp only [collectiveMatrix_none, brightVector, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Pi.smul_apply, smul_eq_mul]
    rw [← ht]
    ring
  | some i =>
    simp [collectiveMatrix_some, brightVector]

theorem darkVector_kernel (m : ℕ) (b : ℝ)
    (v : Option (Fin m) → ℝ) (h0 : v none = 0)
    (hs : ∑ j : Fin m, v (some j) = 0) :
    collectiveMatrix m b *ᵥ v = 0 := by
  funext i
  cases i with
  | none => simp [collectiveMatrix_none, hs]
  | some i => simp [collectiveMatrix_some, h0]

theorem kernel_iff (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : b ≠ 0)
    (v : Option (Fin m) → ℝ) :
    collectiveMatrix m b *ᵥ v = 0 ↔
      v none = 0 ∧ ∑ j : Fin m, v (some j) = 0 := by
  constructor
  · intro h
    have hnone := congrFun h none
    have hsome := congrFun h (some ⟨0, hm⟩)
    simp only [collectiveMatrix_none, Pi.zero_apply] at hnone
    simp only [collectiveMatrix_some, Pi.zero_apply] at hsome
    exact ⟨(mul_eq_zero.mp hsome).resolve_left hb,
      (mul_eq_zero.mp hnone).resolve_left hb⟩
  · rintro ⟨h0, hs⟩
    exact darkVector_kernel m b v h0 hs

theorem bright_hasEigenvector (m : ℕ) (hm : 0 < m) (b t : ℝ)
    (ht : t ^ 2 = (m : ℝ)) :
    Module.End.HasEigenvector (collectiveMatrix m b).mulVecLin (b * t)
      (brightVector m t) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr (brightVector_eigen m b t ht), ?_⟩
  intro h
  have hx := congrFun h (some ⟨0, hm⟩)
  simp [brightVector] at hx

theorem nonzero_eigenvalue_square (m : ℕ) (b μ : ℝ) (hμ : μ ≠ 0)
    (v : Option (Fin m) → ℝ) (hv : v ≠ 0)
    (he : collectiveMatrix m b *ᵥ v = μ • v) :
    μ ^ 2 = (m : ℝ) * b ^ 2 := by
  have hnone := congrFun he none
  simp only [collectiveMatrix_none, Pi.smul_apply, smul_eq_mul] at hnone
  have hsome (i : Fin m) : b * v none = μ * v (some i) := by
    have h := congrFun he (some i)
    simpa only [collectiveMatrix_some, Pi.smul_apply, smul_eq_mul] using h
  have hx : v none ≠ 0 := by
    intro h0
    apply hv
    funext i
    cases i with
    | none => exact h0
    | some i =>
      have h := hsome i
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hμ
  have hsum := congrArg (fun f : Fin m → ℝ => ∑ i, f i) (funext hsome)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hpoly : (μ ^ 2 - (m : ℝ) * b ^ 2) * v none = 0 := by
    nlinarith [congrArg (fun x : ℝ => b * x) hsum,
      congrArg (fun x : ℝ => μ * x) hnone]
  have hz := (mul_eq_zero.mp hpoly).resolve_right hx
  exact sub_eq_zero.mp hz

theorem eigenvalue_trichotomy (m : ℕ) (b μ : ℝ)
    (he : Module.End.HasEigenvalue (collectiveMatrix m b).mulVecLin μ) :
    μ = 0 ∨ μ = b * Real.sqrt m ∨ μ = -(b * Real.sqrt m) := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · right
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hs := nonzero_eigenvalue_square m b μ hμ v hv.2 hv.apply_eq_smul
    have hsq : μ ^ 2 = (b * Real.sqrt m) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
      simpa [mul_comm] using hs
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

def effectiveMatrix (m : ℕ) : Matrix (Option (Fin m)) (Option (Fin m)) ℝ :=
  collectiveMatrix m ((3 / Real.sqrt 8) / Real.sqrt m)

theorem effective_positive_mode (m : ℕ) (hm : 0 < m) :
    Module.End.HasEigenvector (effectiveMatrix m).mulVecLin (3 / Real.sqrt 8)
      (brightVector m (Real.sqrt m)) := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hm)
  have h := bright_hasEigenvector m hm ((3 / Real.sqrt 8) / Real.sqrt m)
    (Real.sqrt m) (Real.sq_sqrt (Nat.cast_nonneg m))
  simpa [effectiveMatrix, div_mul_cancel₀ _ hs] using h

theorem effective_negative_mode (m : ℕ) (hm : 0 < m) :
    Module.End.HasEigenvector (effectiveMatrix m).mulVecLin (-(3 / Real.sqrt 8))
      (brightVector m (-Real.sqrt m)) := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hm)
  have ht : (-Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := by
    rw [neg_sq, Real.sq_sqrt (Nat.cast_nonneg m)]
  have h := bright_hasEigenvector m hm ((3 / Real.sqrt 8) / Real.sqrt m)
    (-Real.sqrt m) ht
  simpa [effectiveMatrix, mul_neg, div_mul_cancel₀ _ hs] using h

theorem effective_eigenvalue_trichotomy (m : ℕ) (hm : 0 < m) (μ : ℝ)
    (he : Module.End.HasEigenvalue (effectiveMatrix m).mulVecLin μ) :
    μ = 0 ∨ μ = 3 / Real.sqrt 8 ∨ μ = -(3 / Real.sqrt 8) := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hm)
  have h := eigenvalue_trichotomy m ((3 / Real.sqrt 8) / Real.sqrt m) μ he
  simpa [div_mul_cancel₀ _ hs] using h

#print axioms collectiveMatrix_none
#print axioms collectiveMatrix_some
#print axioms brightVector_eigen
#print axioms darkVector_kernel
#print axioms kernel_iff
#print axioms bright_hasEigenvector
#print axioms nonzero_eigenvalue_square
#print axioms eigenvalue_trichotomy
#print axioms effective_positive_mode
#print axioms effective_negative_mode
#print axioms effective_eigenvalue_trichotomy

end

end GrowingDefects
