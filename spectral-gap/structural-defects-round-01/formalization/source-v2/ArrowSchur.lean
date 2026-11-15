import PortEnergy
import Mathlib.Tactic.Linarith

namespace StructuralDefects

open Matrix

noncomputable section

variable {η : Type*} [Fintype η] [DecidableEq η]

def diagonalResolvent (z : ℝ) (w : η → ℝ) : Matrix η η ℝ :=
  Matrix.diagonal (fun i => (z - w i)⁻¹)

theorem diagonal_resolvent_right (z : ℝ) (w : η → ℝ) (hz : ∀ i, z - w i ≠ 0) :
    (z • (1 : Matrix η η ℝ) - Matrix.diagonal w) * diagonalResolvent z w = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalResolvent, Matrix.mul_diagonal, Matrix.sub_apply,
      Matrix.smul_apply, hz]
  · simp [diagonalResolvent, Matrix.mul_diagonal, Matrix.sub_apply,
      Matrix.smul_apply, hij]

theorem diagonal_resolvent_left (z : ℝ) (w : η → ℝ) (hz : ∀ i, z - w i ≠ 0) :
    diagonalResolvent z w * (z • (1 : Matrix η η ℝ) - Matrix.diagonal w) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalResolvent, Matrix.diagonal_mul, Matrix.sub_apply,
      Matrix.smul_apply, hz]
  · simp [diagonalResolvent, Matrix.diagonal_mul, Matrix.sub_apply,
      Matrix.smul_apply, hij]

theorem diagonal_resolvent_quadratic (z : ℝ) (w b : η → ℝ) :
    b ⬝ᵥ (diagonalResolvent z w *ᵥ b) = ∑ i, b i ^ 2 / (z - w i) := by
  simp only [diagonalResolvent, dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def arrowMatrix (a : ℝ) (b w : η → ℝ) : Matrix (Unit ⊕ η) (Unit ⊕ η) ℝ :=
  Matrix.fromBlocks (fun _ _ => a) (fun _ j => b j) (fun i _ => b i) (Matrix.diagonal w)

def arrowWitness (z : ℝ) (w b : η → ℝ) : Unit ⊕ η → ℝ :=
  Sum.elim (fun _ => 1) (diagonalResolvent z w *ᵥ b)

omit [Fintype η] in
theorem arrowMatrix_symmetric (a : ℝ) (b w : η → ℝ) :
    (arrowMatrix a b w).transpose = arrowMatrix a b w := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      by_cases hij : i = j
      · subst j
        rfl
      · simp [arrowMatrix, Matrix.transpose_apply, hij, Ne.symm hij]

theorem arrow_schur_witness (a z : ℝ) (b w : η → ℝ) (hz : ∀ i, z - w i ≠ 0) :
    z * (arrowWitness z w b ⬝ᵥ arrowWitness z w b) -
      arrowWitness z w b ⬝ᵥ (arrowMatrix a b w *ᵥ arrowWitness z w b) =
        z - a - ∑ i, b i ^ 2 / (z - w i) := by
  let v := diagonalResolvent z w *ᵥ b
  have hs : (z • (1 : Matrix η η ℝ) - Matrix.diagonal w) *ᵥ v = b := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, diagonal_resolvent_right z w hz, Matrix.one_mulVec]
  have he := congrArg (fun x => v ⬝ᵥ x) hs
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at he
  have hq : v ⬝ᵥ b = ∑ i, b i ^ 2 / (z - w i) := by
    rw [dotProduct_comm]
    exact diagonal_resolvent_quadratic z w b
  change z * ((Sum.elim (fun _ : Unit => (1 : ℝ)) v) ⬝ᵥ Sum.elim (fun _ => 1) v) -
    (Sum.elim (fun _ : Unit => (1 : ℝ)) v) ⬝ᵥ
      (arrowMatrix a b w *ᵥ Sum.elim (fun _ => 1) v) = _
  simp only [arrowMatrix, Matrix.fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, sumElim_dotProduct_sumElim, dotProduct_add]
  have htop : ((fun _ _ : Unit => a) : Matrix Unit Unit ℝ) *ᵥ (fun _ => 1) =
      fun _ => a := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hbottom : ((fun i (_ : Unit) => b i) : Matrix η Unit ℝ) *ᵥ (fun _ => 1) = b := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hrow : ((fun (_ : Unit) j => b j) : Matrix Unit η ℝ) *ᵥ v = fun _ => b ⬝ᵥ v := rfl
  rw [htop, hbottom, hrow]
  simp only [dotProduct, Fintype.sum_unique, one_mul, mul_one]
  change z * (1 + v ⬝ᵥ v) - (a + b ⬝ᵥ v + (v ⬝ᵥ b + v ⬝ᵥ (Matrix.diagonal w *ᵥ v))) = _
  rw [dotProduct_comm b v, hq]
  nlinarith [he]

def pairWeights (w0 : ℝ) (w : η → ℝ) : Option η → ℝ
  | none => w0
  | some i => w i

def leadingPairColumn (k : ℝ) (w : η → ℝ) : Option η → ℝ
  | none => k
  | some i => -w i

def referenceCorrection : Option (Option η) → ℝ
  | some (some _) => -1
  | _ => 0

def baseArrow (k w0 : ℝ) (w : η → ℝ) : Matrix (Option (Option η)) (Option (Option η)) ℝ :=
  Matrix.diagonal (fun i => match i with
    | none => -k
    | some j => pairWeights w0 w j)

def firstArrow (k : ℝ) : Matrix (Option (Option η)) (Option (Option η)) ℝ
  | none, some _ => k
  | some _, none => k
  | _, _ => 0

def pairComplement : Matrix (Option (Option η)) (Option (Option η)) ℝ :=
  1 - Matrix.diagonal (Pi.single none 1)

theorem leading_projected_column (k w0 : ℝ) (w : η → ℝ) :
    firstArrow k *ᵥ (Pi.single none 1) +
      (baseArrow k w0 w + k • 1) *ᵥ referenceCorrection =
        fun i => match i with
          | none => 0
          | some j => leadingPairColumn k w j := by
  funext i
  cases i with
  | none => simp [firstArrow, Matrix.add_mulVec, baseArrow, referenceCorrection,
      Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]
  | some j =>
    cases j with
    | none => simp [firstArrow, Matrix.add_mulVec, baseArrow, referenceCorrection,
        Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, pairWeights, leadingPairColumn]
    | some j => simp [firstArrow, Matrix.add_mulVec, baseArrow, referenceCorrection,
        Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, pairWeights, leadingPairColumn]

theorem leading_column_projection (k w0 : ℝ) (w : η → ℝ) :
    pairComplement *ᵥ (firstArrow k *ᵥ (Pi.single none 1) +
      (baseArrow k w0 w + k • 1) *ᵥ referenceCorrection) =
        fun i => match i with
          | none => 0
          | some j => leadingPairColumn k w j := by
  rw [leading_projected_column]
  funext i
  cases i with
  | none => simp [pairComplement, Matrix.sub_mulVec, Matrix.mulVec_diagonal]
  | some j => simp [pairComplement, Matrix.sub_mulVec, Matrix.mulVec_diagonal]

theorem leading_pair_self_energy (k w0 : ℝ) (w : η → ℝ) :
    leadingPairColumn k w ⬝ᵥ
      (diagonalResolvent (-k) (pairWeights w0 w) *ᵥ leadingPairColumn k w) =
        -(k ^ 2 / (k + w0)) - ∑ i, w i ^ 2 / (k + w i) := by
  rw [diagonal_resolvent_quadratic]
  simp only [Fintype.sum_option, leadingPairColumn, pairWeights, neg_sq]
  have hden : ∀ t : ℝ, -k - t = -(k + t) := by
    intro t
    ring
  simp_rw [hden, div_neg]
  rw [Finset.sum_neg_distrib]
  ring

theorem finite_screened_correction (k : ℝ) (w : η → ℝ)
    (hk : k ≠ 0) (hw : ∀ i, k + w i ≠ 0) :
    (∑ i : Option η, pairWeights k w i) +
      leadingPairColumn k w ⬝ᵥ
        (diagonalResolvent (-k) (pairWeights k w) *ᵥ leadingPairColumn k w) =
      ∑ i : Option η, k * pairWeights k w i / (k + pairWeights k w i) := by
  rw [leading_pair_self_energy]
  simp only [Fintype.sum_option, pairWeights]
  have hscalar : ∀ i, w i - w i ^ 2 / (k + w i) = k * w i / (k + w i) := by
    intro i
    field_simp [hw i]
    ring
  have hbase : k - k ^ 2 / (k + k) = k * k / (k + k) := by
    have htwo : k + k ≠ 0 := by
      intro h
      apply hk
      linarith
    field_simp [htwo]
    ring
  have hsum : (∑ i, (w i - w i ^ 2 / (k + w i))) =
      ∑ i, k * w i / (k + w i) := Finset.sum_congr rfl (fun i hi => hscalar i)
  rw [Finset.sum_sub_distrib] at hsum
  linarith [hsum, hbase]

#print axioms diagonal_resolvent_right
#print axioms diagonal_resolvent_left
#print axioms diagonal_resolvent_quadratic
#print axioms arrowMatrix_symmetric
#print axioms arrow_schur_witness
#print axioms leading_projected_column
#print axioms leading_column_projection
#print axioms leading_pair_self_energy
#print axioms finite_screened_correction

end

end StructuralDefects
