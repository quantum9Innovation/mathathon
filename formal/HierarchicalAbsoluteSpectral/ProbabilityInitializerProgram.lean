import HierarchicalAbsoluteSpectral.ProbabilityInitializer
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeCost

/-! Executed Gaussian range initializer. Matrix products and range algebra
are the verified fast kernels; every residual entry, square, addition,
scalar root, comparison and bracket division is charged. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

def initializerSumProgram : (n : ℕ) → (Fin n → ℝ) → ArithmeticProgram ℝ
  | 0, _ => .pure 0
  | n+1, x => do
      let s ← initializerSumProgram n (fun i => x i.succ)
      add (x 0) s

@[simp] theorem initializerSumProgram_eval (n : ℕ) (x : Fin n → ℝ) :
    (initializerSumProgram n x).eval = ∑ i, x i := by
  induction n with
  | zero => simp [initializerSumProgram]
  | succ n ih => simp [initializerSumProgram, ih, Fin.sum_univ_succ]

@[simp] theorem initializerSumProgram_work (n : ℕ) (x : Fin n → ℝ) :
    (initializerSumProgram n x).work = n := by
  induction n with
  | zero => simp [initializerSumProgram]
  | succ n ih => simp [initializerSumProgram, ih, Nat.add_comm]

theorem initializerSumProgram_admissible (n : ℕ) (x : Fin n → ℝ) :
    (initializerSumProgram n x).admissible := by
  induction n with
  | zero => trivial
  | succ n ih => simp [initializerSumProgram, ih]

def matrixEnergyProgram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ArithmeticProgram ℝ := do
  let cols ← tabulate n (fun j => do
    let squares ← tabulate m (fun i => mul (A i j) (A i j))
    initializerSumProgram m squares)
  initializerSumProgram n cols

@[simp] theorem matrixEnergyProgram_eval {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixEnergyProgram A).eval = ∑ j, ∑ i, (A i j)^2 := by simp [matrixEnergyProgram, pow_two]

@[simp] theorem matrixEnergyProgram_work {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixEnergyProgram A).work = 2*m*n+n := by simp [matrixEnergyProgram]; ring

theorem matrixEnergyProgram_admissible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixEnergyProgram A).admissible := by simp [matrixEnergyProgram, initializerSumProgram_admissible]

def matrixFrobeniusProgram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ArithmeticProgram ℝ := do
  let e ← matrixEnergyProgram A
  sqrt e

@[simp] theorem matrixFrobeniusProgram_eval {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixFrobeniusProgram A).eval = matrixFrobeniusValue A := by simp [matrixFrobeniusProgram, matrixFrobeniusValue]

@[simp] theorem matrixFrobeniusProgram_work {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixFrobeniusProgram A).work = 2*m*n+n+1 := by simp [matrixFrobeniusProgram]

theorem matrixFrobeniusProgram_admissible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixFrobeniusProgram A).admissible := by
  simp only [matrixFrobeniusProgram, admissible_bind, matrixEnergyProgram_admissible,
    matrixEnergyProgram_eval, admissible_sqrt, true_and]
  positivity

def initializerRatioProgram (k : ℕ) (β : ℝ) : ArithmeticProgram ℝ := do
  let s ← sqrt (k : ℝ)
  let a ← mul 100 (k : ℝ)
  let t ← div a β
  let sq ← mul t t
  let cube ← mul sq t
  let c ← add 1 cube
  mul s c

@[simp] theorem initializerRatioProgram_eval (k : ℕ) (β : ℝ) :
    (initializerRatioProgram k β).eval = initializerRatio k β := by
  simp [initializerRatioProgram, initializerRatio, gaussianCaptureRadius, pow_succ]

@[simp] theorem initializerRatioProgram_work (k : ℕ) (β : ℝ) :
    (initializerRatioProgram k β).work = 7 := by simp [initializerRatioProgram]

theorem initializerRatioProgram_admissible (k : ℕ) (β : ℝ) (hβ : β ≠ 0) :
    (initializerRatioProgram k β).admissible := by simp [initializerRatioProgram, hβ]

inductive InitializerResult where
  | exact
  | bracket (lower upper : ℝ)
  deriving DecidableEq

def initializerBracketProgram (τ C : ℝ) : ArithmeticProgram InitializerResult :=
  .branch τ 0 (fun _ => .pure .exact) (fun _ => do
    let lower ← div τ C
    ArithmeticProgram.pure (.bracket lower τ))

@[simp] theorem initializerBracketProgram_eval (τ C : ℝ) :
    (initializerBracketProgram τ C).eval = if τ ≤ 0 then .exact else .bracket (τ/C) τ := by
  by_cases h : τ ≤ 0 <;> simp [initializerBracketProgram, ArithmeticProgram.eval, h]

theorem initializerBracketProgram_work (τ C : ℝ) :
    (initializerBracketProgram τ C).work ≤ 2 := by
  by_cases h : τ ≤ 0 <;> simp [initializerBracketProgram, ArithmeticProgram.work, h]

theorem initializerBracketProgram_admissible (τ C : ℝ) (hC : C ≠ 0) :
    (initializerBracketProgram τ C).admissible := by
  by_cases h : τ ≤ 0 <;> simp [initializerBracketProgram, ArithmeticProgram.admissible, h, hC]

structure InitializerComputation {k r : ℕ} (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) where
  raw : Matrix (Fin k) (Fin r) ℝ
  raw_eq : raw = T*Ξ
  range : OrthogonalRange raw
  value : ℝ
  value_eq : value = initializerValue T range.basis
  result : InitializerResult
  result_eq : result = if value ≤ 0 then .exact else .bracket (value/initializerRatio k β) value

def gaussianInitializerProgram {k r : ℕ}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) :
    ArithmeticProgram (InitializerComputation T Ξ β) := do
  let Y ← certify ((kernels k k r).program T Ξ)
  let out ← orthogonalRangeProgram kernels Y.val
  let q ← certify ((kernels out.dimension k k).program out.basisᵀ T)
  let P ← certify ((kernels k out.dimension k).program out.basis q.val)
  let B ← certify (blockSubProgram T P.val)
  let τ ← certify (matrixFrobeniusProgram B.val)
  let C ← certify (initializerRatioProgram k β)
  let result ← certify (initializerBracketProgram τ.val C.val)
  have hq : q.val = out.basisᵀ*T := q.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hP : P.val = out.basis*(out.basisᵀ*T) := by
    rw [P.property, ArithmeticKernel.program_eval, hq]
  have hB : B.val = initializerResidual T out.basis := by
    rw [B.property, blockSubProgram_eval, hP]
  ArithmeticProgram.pure {
    raw := Y.val
    raw_eq := Y.property.trans (ArithmeticKernel.program_eval _ _ _)
    range := out
    value := τ.val
    value_eq := by rw [τ.property, matrixFrobeniusProgram_eval, hB]; rfl
    result := result.val
    result_eq := by rw [result.property, initializerBracketProgram_eval,
      C.property, initializerRatioProgram_eval] }

theorem gaussianInitializerProgram_admissible {k r : ℕ}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hk : 1 ≤ k) (hβ : 0 < β) :
    (gaussianInitializerProgram kernels T Ξ β).admissible := by
  simp only [gaussianInitializerProgram, admissible_bind, certify_admissible,
    ArithmeticKernel.program_admissible, orthogonalRangeProgram_admissible,
    blockSubProgram_admissible, matrixFrobeniusProgram_admissible,
    initializerRatioProgram_admissible k β hβ.ne',
    certify_eval, initializerRatioProgram_eval,
    initializerBracketProgram_admissible _ _ (initializerRatio_pos k β hk hβ).ne',
    admissible_pure, and_self]

theorem InitializerComputation.exact_rank {k r : ℕ} {T : Core k}
    {Ξ : Matrix (Fin k) (Fin r) ℝ} {β : ℝ} (out : InitializerComputation T Ξ β)
    (h : out.result = .exact) : T.rank ≤ r := by
  have ht : out.value ≤ 0 := by
    rw [out.result_eq] at h
    split_ifs at h with ht
    · exact ht
    · contradiction
  have hz : initializerValue T out.range.basis = 0 := by
    rw [out.value_eq] at ht
    exact le_antisymm ht (matrixFrobeniusValue_nonneg _)
  exact (initializer_zero_rank T out.range.basis out.range.dimension_le_cols hz).2

end
end HierarchicalAbsoluteSpectral
