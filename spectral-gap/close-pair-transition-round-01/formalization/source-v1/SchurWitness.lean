import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

namespace ClosePair

noncomputable section

def augmented {ι κ : Type*} (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks A B B.transpose 0

theorem augmented_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (Sum.elim x y) ⬝ᵥ (augmented A B *ᵥ Sum.elim x y) =
      x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) := by
  have hc : y ⬝ᵥ (B.transpose *ᵥ x) = x ⬝ᵥ (B *ᵥ y) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  simp [augmented, Matrix.fromBlocks_mulVec, Function.comp_def,
    sumElim_dotProduct_sumElim, dotProduct_add, hc]
  ring

theorem block_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℝ) (y : κ → ℝ) :
    (Sum.elim x y) ⬝ᵥ (Sum.elim x y) = x ⬝ᵥ x + y ⬝ᵥ y :=
  sumElim_dotProduct_sumElim x x y y

theorem schur_witness_identity
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A R : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (z : ℝ)
    (hR : (z • (1 : Matrix ι ι ℝ) - A) * R = 1) (y : κ → ℝ) :
    let x := R *ᵥ (B *ᵥ y)
    z * ((Sum.elim x y) ⬝ᵥ (Sum.elim x y)) -
        ((Sum.elim x y) ⬝ᵥ (augmented A B *ᵥ Sum.elim x y)) =
      y ⬝ᵥ ((z • (1 : Matrix κ κ ℝ) - B.transpose * R * B) *ᵥ y) := by
  dsimp only
  let x := R *ᵥ (B *ᵥ y)
  have hsolve : (z • (1 : Matrix ι ι ℝ) - A) *ᵥ x = B *ᵥ y := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  have hs := congrArg (fun v => x ⬝ᵥ v) hsolve
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hs
  have hcross : y ⬝ᵥ ((B.transpose * R * B) *ᵥ y) = x ⬝ᵥ (B *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  change z * ((Sum.elim x y) ⬝ᵥ (Sum.elim x y)) -
      ((Sum.elim x y) ⬝ᵥ (augmented A B *ᵥ Sum.elim x y)) = _
  rw [block_norm_sq, augmented_quadratic]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hcross]
  nlinarith

theorem negative_schur_gives_rayleigh
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A R : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (z : ℝ)
    (hR : (z • (1 : Matrix ι ι ℝ) - A) * R = 1) (y : κ → ℝ)
    (hy : y ⬝ᵥ ((z • (1 : Matrix κ κ ℝ) - B.transpose * R * B) *ᵥ y) < 0) :
    let v := Sum.elim (R *ᵥ (B *ᵥ y)) y
    z * (v ⬝ᵥ v) < v ⬝ᵥ (augmented A B *ᵥ v) := by
  have h := schur_witness_identity A R B z hR y
  dsimp only at h ⊢
  linarith

theorem negative_schur_witness_nonzero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A R : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (z : ℝ)
    (hR : (z • (1 : Matrix ι ι ℝ) - A) * R = 1) (y : κ → ℝ)
    (hy : y ⬝ᵥ ((z • (1 : Matrix κ κ ℝ) - B.transpose * R * B) *ᵥ y) < 0) :
    Sum.elim (R *ᵥ (B *ᵥ y)) y ≠ 0 := by
  have h := negative_schur_gives_rayleigh A R B z hR y hy
  dsimp only at h
  intro hv
  rw [hv] at h
  simp at h

theorem actual_inverse_schur_witness
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (z : ℝ)
    [Invertible (z • (1 : Matrix ι ι ℝ) - A)] (y : κ → ℝ)
    (hy : y ⬝ᵥ ((z • (1 : Matrix κ κ ℝ) -
        B.transpose * ⅟(z • (1 : Matrix ι ι ℝ) - A) * B) *ᵥ y) < 0) :
    let v := Sum.elim (⅟(z • (1 : Matrix ι ι ℝ) - A) *ᵥ (B *ᵥ y)) y
    v ≠ 0 ∧ z * (v ⬝ᵥ v) < v ⬝ᵥ (augmented A B *ᵥ v) := by
  exact ⟨negative_schur_witness_nonzero A _ B z (mul_invOf_self _) y hy,
    negative_schur_gives_rayleigh A _ B z (mul_invOf_self _) y hy⟩

#print axioms augmented_quadratic
#print axioms block_norm_sq
#print axioms schur_witness_identity
#print axioms negative_schur_gives_rayleigh
#print axioms negative_schur_witness_nonzero
#print axioms actual_inverse_schur_witness

end

end ClosePair
