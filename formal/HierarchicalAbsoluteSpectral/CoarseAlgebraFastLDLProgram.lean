import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLBlock
import HierarchicalAbsoluteSpectral.CoarseAlgebraPivotSearch
import HierarchicalAbsoluteSpectral.ArithmeticKernel

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

namespace RegularCongruenceData

def replace {n : Type} [Fintype n] [DecidableEq n] {D : Matrix n n ℝ}
    (out : RegularCongruenceData D) (P V : Matrix n n ℝ)
    (hP : P = out.basis) (hV : V = out.inverse) : RegularCongruenceData D where
  basis := P
  inverse := V
  diagonal := out.diagonal
  left_inverse := by rw [hP,hV]; exact out.left_inverse
  right_inverse := by rw [hP,hV]; exact out.right_inverse
  congruence := by rw [hP]; exact out.congruence
  nonzero := out.nonzero

end RegularCongruenceData

def regularEmpty (D : Core 0) : RegularCongruenceData D where
  toCongruenceDiagonalData := CongruenceDiagonalData.ofZero D (Subsingleton.elim _ _)
  nonzero := fun i => i.elim0

def regularSingle (D : Core 1) (hd : D 0 0 ≠ 0) : RegularCongruenceData D where
  basis := 1
  inverse := 1
  diagonal := fun _ => D 0 0
  left_inverse := by simp
  right_inverse := by simp
  congruence := by
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    ext i j
    fin_cases i
    fin_cases j
    simp
  nonzero := fun _ => hd

def regularSingleProgram (D : Core 1) : ArithmeticProgram (Option (RegularCongruenceData D)) := do
  let pivot ← finiteNonzeroSearchProgram (fun _ : Fin 1 => D 0 0)
  ArithmeticProgram.pure (match pivot with
    | .found _ hi => some (regularSingle D hi)
    | .zero _ => none)

theorem regularSingleProgram_admissible (D : Core 1) : (regularSingleProgram D).admissible := by
  simp only [regularSingleProgram, admissible_bind, finiteNonzeroSearchProgram_admissible,
    admissible_pure, and_self]

theorem regularSingleProgram_work (D : Core 1) : (regularSingleProgram D).work ≤ 2 := by
  simp only [regularSingleProgram, work_bind, work_pure, add_zero]
  simpa only [Fintype.card_fin, mul_one] using
    finiteNonzeroSearchProgram_work (fun _ : Fin 1 => D 0 0)

def diagonalInverseProgram {n : ℕ} (d : Fin n → ℝ) : ArithmeticProgram (Core n) := do
  let entries ← tabulate n (fun i => ArithmeticProgram.div 1 (d i))
  ArithmeticProgram.pure (Matrix.diagonal entries)

@[simp] theorem diagonalInverseProgram_eval {n : ℕ} (d : Fin n → ℝ) :
    (diagonalInverseProgram d).eval = Matrix.diagonal (fun i => (d i)⁻¹) := by
  simp [diagonalInverseProgram]

@[simp] theorem diagonalInverseProgram_work {n : ℕ} (d : Fin n → ℝ) :
    (diagonalInverseProgram d).work = n := by simp [diagonalInverseProgram]

theorem diagonalInverseProgram_admissible {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (diagonalInverseProgram d).admissible := by simp [diagonalInverseProgram, hd]

def fastInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    (n : ℕ) → (D : Core n) → Dᵀ = D → ArithmeticProgram (Option (RegularCongruenceData D))
  | 0, D, _ => ArithmeticProgram.pure (some (regularEmpty D))
  | 1, D, _ => regularSingleProgram D
  | n+2, D, hD => by
    let l := (n+2)/2
    let r := n+2-l
    have hl : l < n+2 := by dsimp [l]; omega
    have hr : r < n+2 := by dsimp [r,l]; omega
    have he : l+r = n+2 := by dsimp [l,r]; omega
    let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
    let D' := D.submatrix e e
    have hHerm : D.IsHermitian := by simpa only [Matrix.IsHermitian,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hD
    have hp : D'.IsHermitian := hHerm.submatrix e
    have hb := hermitian_block_decomposition D' hp
    have hA : D'.toBlocks₁₁ᵀ = D'.toBlocks₁₁ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.toBlocks₁₁, Matrix.submatrix]
        using (hp.submatrix Sum.inl).eq
    have hC : D'.toBlocks₂₂ᵀ = D'.toBlocks₂₂ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.toBlocks₂₂, Matrix.submatrix]
        using (hp.submatrix Sum.inr).eq
    exact do
      let left? ← fastInertiaProgram kernels l D'.toBlocks₁₁ hA
      match left? with
      | none => ArithmeticProgram.pure none
      | some left => do
        let invD ← certify (diagonalInverseProgram left.diagonal)
        let A1 ← certify ((kernels l l l).program left.basis invD.val)
        let Ai ← certify ((kernels l l l).program A1.val left.basisᵀ)
        have hAi : Ai.val = left.inverseMatrix := by
          simp only [Ai.property, ArithmeticKernel.program_eval, A1.property, invD.property,
            diagonalInverseProgram_eval, RegularCongruenceData.inverseMatrix]
        let W ← certify ((kernels l l r).program Ai.val D'.toBlocks₁₂)
        have hW : W.val = left.inverseMatrix*D'.toBlocks₁₂ := by
          simp only [W.property, ArithmeticKernel.program_eval, hAi]
        let R ← certify ((kernels r l r).program D'.toBlocks₁₂ᵀ W.val)
        let T ← certify (blockSubProgram D'.toBlocks₂₂ R.val)
        have hT : T.val = regularBlockSchur left D'.toBlocks₁₂ D'.toBlocks₂₂ := by
          simp only [T.property, blockSubProgram_eval, R.property, ArithmeticKernel.program_eval,
            hW, regularBlockSchur]
        have hTsym : T.valᵀ = T.val := by
          rw [hT]
          simp only [regularBlockSchur, Matrix.transpose_sub, Matrix.transpose_mul,
            Matrix.transpose_transpose, Matrix.diagonal_transpose,hC, left.inverseMatrix_transpose, Matrix.mul_assoc]
        let right? ← fastInertiaProgram kernels r T.val hTsym
        match right? with
        | none => ArithmeticProgram.pure none
        | some right => do
          let H ← certify ((kernels l r r).program W.val right.basis)
          let N ← certify (blockScaleProgram (-1) H.val)
          let U ← certify ((kernels l l r).program left.inverse W.val)
          have hN : N.val = -((left.inverseMatrix*D'.toBlocks₁₂)*right.basis) := by
            simp only [N.property, blockScaleProgram_eval, H.property, ArithmeticKernel.program_eval,
              hW, neg_one_smul]
          have hU : U.val = left.inverse*(left.inverseMatrix*D'.toBlocks₁₂) := by
            simp only [U.property, ArithmeticKernel.program_eval, hW]
          let expected := regularBlockData left D'.toBlocks₁₂ D'.toBlocks₂₂ right hT
          let raw := expected.replace
            (Matrix.fromBlocks left.basis N.val 0 right.basis)
            (Matrix.fromBlocks left.inverse U.val 0 right.inverse)
            (by dsimp [expected, regularBlockData]; simp only [hN])
            (by dsimp [expected, regularBlockData]; simp only [hU])
          let pair := raw.cast hb
          ArithmeticProgram.pure (some ((pair.reindex e.symm).cast (by
            ext i j
            simp [D', Matrix.submatrix_apply])))
termination_by n => n
decreasing_by all_goals assumption

theorem fastInertiaProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) : (fastInertiaProgram kernels n D hD).admissible := by
  have hdiag (a : ℕ) (A : Core a) (left : RegularCongruenceData A) :
      (diagonalInverseProgram left.diagonal).admissible :=
    diagonalInverseProgram_admissible _ left.nonzero
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [fastInertiaProgram]; trivial
    · rw [fastInertiaProgram]; exact regularSingleProgram_admissible D
    · have hl : (n+2)/2 < n+2 := by omega
      have hr : n+2-(n+2)/2 < n+2 := by omega
      have ihl := ih _ hl
      have ihr := ih _ hr
      rw [fastInertiaProgram]
      simp only [admissible_bind, ihl, true_and]
      split
      · trivial
      · simp only [admissible_bind, certify_admissible, hdiag, ArithmeticKernel.program_admissible,
          blockSubProgram_admissible, ihr, true_and]
        split
        · trivial
        · simp only [admissible_bind, certify_admissible, ArithmeticKernel.program_admissible,
            blockScaleProgram_admissible, admissible_pure, and_self]

def fastInertiaDiagonalProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal D)) := do
  let out ← fastInertiaProgram kernels n D hD
  ArithmeticProgram.pure (out.map (fun data => data.toCongruenceDiagonalData.toFinite))

theorem fastInertiaDiagonalProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) : (fastInertiaDiagonalProgram kernels n D hD).admissible := by
  simp only [fastInertiaDiagonalProgram, admissible_bind, fastInertiaProgram_admissible,
    admissible_pure, and_self]

theorem fastInertiaDiagonalProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) :
    (fastInertiaDiagonalProgram kernels n D hD).work = (fastInertiaProgram kernels n D hD).work := by
  simp only [fastInertiaDiagonalProgram, work_bind, work_pure, add_zero]

end
end HierarchicalAbsoluteSpectral
