import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileFieldOnly
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertia

/-!
The dual of a congruence-diagonal basis, restricted to its negative entries.
The selection is computed with one scalar comparison per diagonal entry.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

structure ExactGramNegativeSelection {k : ℕ} (d : Fin k → ℝ) where
  width : ℕ
  width_le : width ≤ k
  selected : Fin width ↪ Fin k
  negative : ∀ j, d (selected j) < 0
  complete : ∀ i, d i < 0 → ∃ j, selected j = i
  width_eq : width = (Finset.univ.filter (fun i => d i < 0)).card

def exactGramNegativeSelectionOfMask {k : ℕ} (d : Fin k → ℝ) (mask : Fin k → Bool)
    (hm : ∀ i, mask i = true ↔ d i < 0) : ExactGramNegativeSelection d := by
  let I := {i : Fin k // mask i = true}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let selected : Fin (Fintype.card I) ↪ Fin k :=
    ⟨fun j => (e.symm j).val, fun _ _ h => e.symm.injective (Subtype.ext h)⟩
  refine ⟨Fintype.card I, ?_, selected, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective selected selected.injective
  · intro j
    exact (hm _).mp (e.symm j).property
  · intro i hi
    refine ⟨e ⟨i,(hm i).mpr hi⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply _)
  · change Fintype.card {i : Fin k // mask i = true} = _
    simp only [Fintype.card_subtype, hm]

def exactGramNegativeMaskProgram {k : ℕ} (d : Fin k → ℝ) : ArithmeticProgram (Fin k → Bool) :=
  tabulate k (fun i => .branch 0 (d i)
    (fun _ => ArithmeticProgram.pure false) (fun _ => ArithmeticProgram.pure true))

theorem exactGramNegativeMaskProgram_eval {k : ℕ} (d : Fin k → ℝ) (i : Fin k) :
    (exactGramNegativeMaskProgram d).eval i = true ↔ d i < 0 := by
  simp only [exactGramNegativeMaskProgram, eval_tabulate, eval]
  by_cases hi : 0 ≤ d i
  · simp [hi, not_lt_of_ge hi]
  · simp [hi, lt_of_not_ge hi]

theorem exactGramNegativeMaskProgram_work {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeMaskProgram d).work = k := by
  simp [exactGramNegativeMaskProgram, work]

theorem exactGramNegativeMaskProgram_admissible {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeMaskProgram d).admissible := by
  simp [exactGramNegativeMaskProgram, admissible]

theorem exactGramNegativeMaskProgram_fieldOnly {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeMaskProgram d).rankProfileFieldOnly := by
  simp [exactGramNegativeMaskProgram, rankProfileFieldOnly]

def exactGramNegativeSelectionProgram {k : ℕ} (d : Fin k → ℝ) :
    ArithmeticProgram (ExactGramNegativeSelection d) := do
  let mask ← certify (exactGramNegativeMaskProgram d)
  have hm : ∀ i, mask.val i = true ↔ d i < 0 := by
    rw [mask.property]
    exact exactGramNegativeMaskProgram_eval d
  ArithmeticProgram.pure (exactGramNegativeSelectionOfMask d mask.val hm)

theorem exactGramNegativeSelectionProgram_work {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeSelectionProgram d).work = k := by
  simp only [exactGramNegativeSelectionProgram, work_bind, certify_work,
    exactGramNegativeMaskProgram_work, work_pure, add_zero]

theorem exactGramNegativeSelectionProgram_admissible {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeSelectionProgram d).admissible := by
  simp only [exactGramNegativeSelectionProgram, admissible_bind, certify_admissible,
    exactGramNegativeMaskProgram_admissible, admissible_pure, and_self]

theorem exactGramNegativeSelectionProgram_fieldOnly {k : ℕ} (d : Fin k → ℝ) :
    (exactGramNegativeSelectionProgram d).rankProfileFieldOnly := by
  simp only [exactGramNegativeSelectionProgram, rankProfileFieldOnly_bind, rankProfileFieldOnly_certify,
    exactGramNegativeMaskProgram_fieldOnly, rankProfileFieldOnly_pure, and_self]

theorem FiniteCongruenceDiagonal.form_eq {k : ℕ} {K : Core k}
    (out : FiniteCongruenceDiagonal K) :
    K = out.inverseᵀ * Matrix.diagonal out.diagonal * out.inverse := by
  calc
    _ = out.inverseᵀ * (out.basisᵀ * K * out.basis) * out.inverse := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, out.right_inverse,
        Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc, out.right_inverse, Matrix.mul_one]
    _ = _ := by rw [out.congruence]

theorem FiniteCongruenceDiagonal.quadratic_nonneg_of_negative_zero {k : ℕ} {K : Core k}
    (out : FiniteCongruenceDiagonal K) (y : Fin k → ℝ)
    (hz : ∀ i, out.diagonal i < 0 → (out.inverse *ᵥ y) i = 0) :
    0 ≤ quadratic K y := by
  rw [out.form_eq]
  have hq := quadratic_congruence (Matrix.diagonal out.diagonal) out.inverseᵀ y
  simp only [Matrix.transpose_transpose] at hq
  rw [hq]
  simp only [quadratic, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : out.diagonal i < 0
  · simp [hz i hi]
  · nlinarith [mul_nonneg (le_of_not_gt hi) (sq_nonneg ((out.inverse *ᵥ y) i))]

def exactGramDualSmall {m k : ℕ} (T : Matrix (Fin m) (Fin k) ℝ)
    {K : Core k} (out : FiniteCongruenceDiagonal K) (s : ExactGramNegativeSelection out.diagonal) :
    Matrix (Fin m) (Fin s.width) ℝ := T * out.inverseᵀ.submatrix id s.selected

theorem exactGramDualLift_complement {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    {K : Core k} (out : FiniteCongruenceDiagonal K) (s : ExactGramNegativeSelection out.diagonal)
    (x : Fin n → ℝ) (hx : (Z * out.inverseᵀ.submatrix id s.selected)ᵀ *ᵥ x = 0) :
    0 ≤ quadratic K (Zᵀ *ᵥ x) := by
  apply out.quadratic_nonneg_of_negative_zero
  intro i hi
  obtain ⟨j,hj⟩ := s.complete i hi
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec] at hx
  have hh := congrFun hx j
  change (out.inverse *ᵥ (Zᵀ *ᵥ x)) (s.selected j) = 0 at hh
  simpa only [hj] using hh

end
end HierarchicalAbsoluteSpectral
