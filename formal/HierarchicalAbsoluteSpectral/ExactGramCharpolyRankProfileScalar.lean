import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileOrdered
import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def rankProfileMulProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    ArithmeticProgram (Matrix (Fin a) (Fin c) ℝ) :=
  if max a (max b c) = 0 then ArithmeticProgram.pure 0 else (kernels a b c).program A B

@[simp] theorem rankProfileMulProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    (rankProfileMulProgram kernels A B).eval = A * B := by
  unfold rankProfileMulProgram
  split_ifs with hz
  · have ha : a = 0 := by omega
    subst a
    exact Subsingleton.elim _ _
  · exact ArithmeticKernel.program_eval _ _ _

@[simp] theorem rankProfileMulProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    (rankProfileMulProgram kernels A B).admissible := by
  unfold rankProfileMulProgram
  split_ifs <;> simp only [admissible_pure, ArithmeticKernel.program_admissible]

theorem rankProfileMulProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ)
    (N : ℕ) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    (rankProfileMulProgram kernels A B).work ≤ kernelEnvelope kernels N := by
  unfold rankProfileMulProgram
  split_ifs with hz
  · simp only [work_pure, Nat.zero_le]
  · rw [ArithmeticKernel.program_work]
    exact kernelEnvelope_le kernels N a b c ha hb hc (by omega)

def fieldPrincipalEmpty (D : Core 0) : FieldOrderedPSDPrincipalData D where
  dimension := 0
  selected := Fin.elim0
  selected_injective := fun i => i.elim0
  coordinates := 0
  inverse := 0
  interpolation := Subsingleton.elim _ _
  left_inverse := Subsingleton.elim _ _
  right_inverse := Subsingleton.elim _ _
  decomposition := Subsingleton.elim _ _
  selected_strictMono := fun i => i.elim0
  prefix_zero := fun i => i.elim0

def fieldPrincipalZeroSingle (D : Core 1) (hd : D 0 0 = 0) :
    FieldOrderedPSDPrincipalData D where
  dimension := 0
  selected := Fin.elim0
  selected_injective := fun i => i.elim0
  coordinates := 0
  inverse := 0
  interpolation := Subsingleton.elim _ _
  left_inverse := Subsingleton.elim _ _
  right_inverse := Subsingleton.elim _ _
  decomposition := by
    simp only [Matrix.transpose_zero, Matrix.zero_mul]
    ext i j
    fin_cases i
    fin_cases j
    exact hd.symm
  selected_strictMono := fun i => i.elim0
  prefix_zero := fun i => i.elim0

def fieldPrincipalNonzeroSingle (D : Core 1) (hd : D 0 0 ≠ 0)
    (x : ℝ) (hx : x = 1 / D 0 0) : FieldOrderedPSDPrincipalData D where
  dimension := 1
  selected := id
  selected_injective := Function.injective_id
  coordinates := 1
  inverse := fun _ _ => x
  interpolation := rfl
  left_inverse := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, hx, hd]
  right_inverse := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, hx, hd]
  decomposition := by simp
  selected_strictMono := strictMono_id
  prefix_zero := by
    intro i j hj
    fin_cases i
    fin_cases j
    exact (lt_irrefl _ hj).elim

def fieldPrincipalSingleProgram (D : Core 1) (hD : D.PosSemidef) :
    ArithmeticProgram (FieldOrderedPSDPrincipalData D) :=
  .branch (D 0 0) 0
    (fun hz => ArithmeticProgram.pure (fieldPrincipalZeroSingle D (le_antisymm hz hD.diag_nonneg)))
    (fun hp => do
      let x ← certify (ArithmeticProgram.div 1 (D 0 0))
      ArithmeticProgram.pure (fieldPrincipalNonzeroSingle D (lt_of_not_ge hp).ne'
        x.val (x.property.trans (eval_div _ _))))

theorem fieldPrincipalSingleProgram_admissible (D : Core 1) (hD : D.PosSemidef) :
    (fieldPrincipalSingleProgram D hD).admissible := by
  by_cases hz : D 0 0 ≤ 0
  · simp only [fieldPrincipalSingleProgram, admissible, dif_pos hz]
  · simp only [fieldPrincipalSingleProgram, admissible, dif_neg hz, admissible_bind,
      certify_admissible, admissible_div, admissible_pure, and_true]
    exact (lt_of_not_ge hz).ne'

theorem fieldPrincipalSingleProgram_work (D : Core 1) (hD : D.PosSemidef) :
    (fieldPrincipalSingleProgram D hD).work ≤ 2 := by
  simp only [fieldPrincipalSingleProgram, work]
  split_ifs
  · norm_num [work]
  · simp only [work_bind, certify_work, work_div, work_pure]
    norm_num

end
end HierarchicalAbsoluteSpectral
