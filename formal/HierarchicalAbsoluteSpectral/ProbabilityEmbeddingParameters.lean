import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingGram
import HierarchicalAbsoluteSpectral.ThresholdHalving

/-! Counted scalar parameter selection: halving determines the moment order,
and at most n comparisons compute the capped row count. Logs and ceilings
appear only in specifications and bounds. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix SRHT
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

def embeddingMomentOrder (m : ℕ) (δ : ℝ) : ℕ :=
  leastHalvings (4*(m : ℝ)/δ) 1 (by norm_num)+1

def embeddingMomentOrderProgram (m : ℕ) (δ : ℝ) : ArithmeticProgram ℕ := do
  let a ← mul 4 (m : ℝ)
  let b ← div a δ
  let j ← scalarHalving b 1 (by norm_num)
  ArithmeticProgram.pure (j+1)

theorem embeddingMomentOrderProgram_specification (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (embeddingMomentOrderProgram m δ).eval = embeddingMomentOrder m δ ∧
    (embeddingMomentOrderProgram m δ).work = 2*embeddingMomentOrder m δ+1 ∧
    (embeddingMomentOrderProgram m δ).admissible := by
  have hh := scalarHalving_checked (4*(m : ℝ)/δ) 1 (by norm_num)
  simp only [embeddingMomentOrderProgram, eval_bind, eval_mul, eval_div, eval_pure,
    work_bind, work_mul, work_div, work_pure, add_zero, admissible_bind,
    admissible_mul, admissible_div, admissible_pure, true_and, and_true]
  rw [hh.1,hh.2.1]
  exact ⟨rfl,by dsimp [embeddingMomentOrder]; omega,hδ.ne',hh.2.2⟩

theorem embeddingMomentOrder_positive (m : ℕ) (δ : ℝ) : 1 ≤ embeddingMomentOrder m δ := by
  unfold embeddingMomentOrder
  omega

theorem embeddingMomentOrder_failure (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (m : ℝ)*(1/2 : ℝ)^(2*embeddingMomentOrder m δ) ≤ δ := by
  let j := leastHalvings (4*(m : ℝ)/δ) 1 (by norm_num)
  have hs : 4*(m : ℝ)/δ ≤ (2 : ℝ)^j := by
    simpa only [one_mul] using
      (div_le_iff₀ (by positivity)).mp (leastHalvings_spec (4*(m : ℝ)/δ) 1 (by norm_num))
  have hp : (2 : ℝ)^j ≤ (4 : ℝ)^(j+1) := by
    calc
      _ ≤ (4 : ℝ)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ ≤ (4 : ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hm : (m : ℝ) ≤ δ*(4 : ℝ)^(embeddingMomentOrder m δ) := by
    have hb := (div_le_iff₀ hδ).mp (hs.trans hp)
    change (m : ℝ) ≤ δ*(4 : ℝ)^(j+1)
    nlinarith
  have he : (1/2 : ℝ)^(2*embeddingMomentOrder m δ) =
      1/(4 : ℝ)^(embeddingMomentOrder m δ) := by
    rw [pow_mul, ← _root_.one_div_pow]
    norm_num
  rw [he,mul_one_div]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)

def boundedCeilProgram (x : ℝ) : ℕ → ArithmeticProgram ℕ
  | 0 => ArithmeticProgram.pure 0
  | n+1 => .branch x (n : ℝ)
      (fun _ => boundedCeilProgram x n) (fun _ => ArithmeticProgram.pure (n+1))

theorem boundedCeilProgram_specification (x : ℝ) (n : ℕ) :
    (boundedCeilProgram x n).eval = min n ⌈x⌉₊ ∧
    (boundedCeilProgram x n).work ≤ n ∧ (boundedCeilProgram x n).admissible := by
  induction n with
  | zero => simp [boundedCeilProgram]
  | succ n ih =>
    rw [boundedCeilProgram]
    by_cases hx : x ≤ (n : ℝ)
    · have hc : ⌈x⌉₊ ≤ n := Nat.ceil_le.mpr hx
      simp only [ArithmeticProgram.eval,ArithmeticProgram.work,ArithmeticProgram.admissible,
        dif_pos hx]
      rw [ih.1,min_eq_right hc,min_eq_right (by omega : ⌈x⌉₊ ≤ n+1)]
      exact ⟨rfl,by omega,ih.2.2⟩
    · have hc : n+1 ≤ ⌈x⌉₊ := Nat.add_one_le_ceil_iff.mpr (lt_of_not_ge hx)
      simp [ArithmeticProgram.eval,ArithmeticProgram.work,ArithmeticProgram.admissible,
        hx,min_eq_left hc]

def scalarNatProgram : ℕ → ArithmeticProgram ℝ
  | 0 => ArithmeticProgram.pure 0
  | n+1 => do
      let x ← scalarNatProgram n
      add x 1

theorem scalarNatProgram_specification (n : ℕ) :
    (scalarNatProgram n).eval = (n : ℝ) ∧ (scalarNatProgram n).work = n ∧
      (scalarNatProgram n).admissible := by
  induction n with
  | zero => simp [scalarNatProgram]
  | succ n ih => simp [scalarNatProgram,ih.1,ih.2.1,ih.2.2,Nat.cast_add,Nat.cast_one]

def embeddingRowTarget (m q : ℕ) (ε : ℝ) : ℝ :=
  8192*(effectiveDimension m q : ℝ)/ε^2

def embeddingRowTargetProgram (m q : ℕ) (ε : ℝ) : ArithmeticProgram ℝ := do
  let a ← scalarNatProgram q
  let b ← mul a a
  let c ← mul b a
  let d ← mul 27 c
  let e ← add (m : ℝ) d
  let f ← mul 8192 e
  let h ← mul ε ε
  div f h

theorem embeddingRowTargetProgram_specification (m q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (embeddingRowTargetProgram m q ε).eval = embeddingRowTarget m q ε ∧
    (embeddingRowTargetProgram m q ε).work = q+7 ∧
    (embeddingRowTargetProgram m q ε).admissible := by
  have hh := scalarNatProgram_specification q
  refine ⟨?_,?_,?_⟩
  · simp only [embeddingRowTargetProgram,eval_bind,eval_mul,eval_add,eval_div,hh.1,
      embeddingRowTarget,effectiveDimension,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  · simp only [embeddingRowTargetProgram,work_bind,work_mul,work_add,work_div,hh.2.1]
  · simp only [embeddingRowTargetProgram,eval_bind,eval_mul,eval_add,eval_div,hh.1,
      admissible_bind,admissible_mul,admissible_add,admissible_div,hh.2.2,true_and]
    exact mul_ne_zero hε.ne' hε.ne'

def embeddingComputedRowCount (n m : ℕ) (ε δ : ℝ) : ℕ :=
  min n ⌈embeddingRowTarget m (embeddingMomentOrder m δ) ε⌉₊

def embeddingRowCountProgram (n m : ℕ) (ε δ : ℝ) : ArithmeticProgram ℕ := do
  let q ← embeddingMomentOrderProgram m δ
  let x ← embeddingRowTargetProgram m q ε
  boundedCeilProgram x n

theorem embeddingRowCountProgram_specification (n m : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    (embeddingRowCountProgram n m ε δ).eval = embeddingComputedRowCount n m ε δ ∧
    (embeddingRowCountProgram n m ε δ).work ≤ n+3*embeddingMomentOrder m δ+8 ∧
    (embeddingRowCountProgram n m ε δ).admissible := by
  have hq := embeddingMomentOrderProgram_specification m δ hδ
  have hx := embeddingRowTargetProgram_specification m (embeddingMomentOrder m δ) ε hε
  have hn := boundedCeilProgram_specification
    (embeddingRowTarget m (embeddingMomentOrder m δ) ε) n
  simp only [embeddingRowCountProgram,eval_bind,work_bind,admissible_bind,hq.1,hx.1]
  rw [hq.2.1,hx.2.1]
  exact ⟨hn.1,by omega,hq.2.2,hx.2.2,hn.2.2⟩

theorem embeddingComputedRowCount_specification (n m : ℕ) (ε δ : ℝ)
    (hn : 0 < n) (hε : 0 < ε) :
    0 < embeddingComputedRowCount n m ε δ ∧ embeddingComputedRowCount n m ε δ ≤ n ∧
      (embeddingComputedRowCount n m ε δ < n →
        embeddingRowTarget m (embeddingMomentOrder m δ) ε ≤ embeddingComputedRowCount n m ε δ) := by
  have hq := embeddingMomentOrder_positive m δ
  have hD : 0 < effectiveDimension m (embeddingMomentOrder m δ) := by
    dsimp [effectiveDimension]
    positivity
  have hx : 0 < embeddingRowTarget m (embeddingMomentOrder m δ) ε := by
    dsimp [embeddingRowTarget]
    positivity
  refine ⟨lt_min hn (Nat.ceil_pos.mpr hx),min_le_left _ _,?_⟩
  intro hlt
  have hc : ⌈embeddingRowTarget m (embeddingMomentOrder m δ) ε⌉₊ < n := by
    simpa only [embeddingComputedRowCount,min_lt_iff,lt_self_iff_false,false_or] using hlt
  rw [embeddingComputedRowCount,min_eq_right hc.le]
  exact Nat.le_ceil _

end
end HierarchicalAbsoluteSpectral
