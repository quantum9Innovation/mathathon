import HierarchicalAbsoluteSpectral.ThresholdKrylovFullMatrix
import HierarchicalAbsoluteSpectral.ThresholdSingularTests
import HierarchicalAbsoluteSpectral.ThresholdRepeatedSafe

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp MeasureTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k r : ℕ}

def dependentTabulate : (N : ℕ) → (α : Fin N → Type) →
    (∀ i, ArithmeticProgram (α i)) → ArithmeticProgram (∀ i, α i)
  | 0, _, _ => .pure (fun i => Fin.elim0 i)
  | N+1, α, f => do
    let a ← f 0
    let rest ← dependentTabulate N (fun i => α i.succ) (fun i => f i.succ)
    .pure (fun i => Fin.cases a rest i)

@[simp] theorem dependentTabulate_eval (N : ℕ) (α : Fin N → Type)
    (f : ∀ i, ArithmeticProgram (α i)) :
    (dependentTabulate N α f).eval = fun i => (f i).eval := by
  induction N with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ N ih =>
    simp only [dependentTabulate,eval_bind,eval_pure,ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem dependentTabulate_admissible (N : ℕ) (α : Fin N → Type)
    (f : ∀ i, ArithmeticProgram (α i)) :
    (dependentTabulate N α f).admissible ↔ ∀ i, (f i).admissible := by
  induction N with
  | zero => simp only [dependentTabulate,admissible_pure,Fin.forall_fin_zero]
  | succ N ih =>
    simp only [dependentTabulate,admissible_bind,admissible_pure,and_true,ih,Fin.forall_fin_succ]

@[simp] theorem dependentTabulate_work (N : ℕ) (α : Fin N → Type)
    (f : ∀ i, ArithmeticProgram (α i)) :
    (dependentTabulate N α f).work = ∑ i : Fin N, (f i).work := by
  induction N with
  | zero => simp [dependentTabulate]
  | succ N ih =>
    simp only [dependentTabulate,work_bind,work_pure,add_zero,ih,Fin.sum_univ_succ]

theorem computedKrylovRitzValue_eq_fixed (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (G : Fin r → Fin k → ℝ) (j : Fin k) :
    computedKrylovRitzValue kernels T hT actions q S G j =
      orderedEigenvalue (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix G))
        (krylovRitzFixedMatrix_isHermitian kernels T hT q _) j := by
  unfold computedKrylovRitzValue
  rw [← (krylovQueryDataProgram kernels T hT actions q _).eval.ritzValue_eq hT j]
  exact krylovQueryDataProgram_ritzValue_eq_fixed kernels T hT actions q _ j

/-- A literal single Krylov trial, including source rotation, computed range,
compressed Gram, fixed-size lift, and two fresh Gaussian inertia calls. -/
def gaussianKrylovRitzTestsProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ) :
    ArithmeticProgram (Option (CertifiedRitzTests
      (computedKrylovRitzValue kernels T hT actions q S G j) ε)) := do
  let M ← gaussianKrylovFullMatrixProgram kernels T hT actions q S source G
  have hM : M.val.IsHermitian := by
    rw [M.property]
    exact krylovRitzFixedMatrix_isHermitian kernels T hT q _
  let tests? ← fixedRitzTestsProgram kernels M.val hM j ε g
  have hvalue : orderedEigenvalue M.val hM j =
      computedKrylovRitzValue kernels T hT actions q S G j := by
    simpa only [M.property] using (computedKrylovRitzValue_eq_fixed kernels T hT actions q S G j).symm
  match tests? with
  | none => .pure none
  | some tests => .pure (some (hvalue ▸ tests))

theorem gaussianKrylovRitzTestsProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ) :
    (gaussianKrylovRitzTestsProgram kernels T hT actions q S source G j ε g).admissible := by
  simp only [gaussianKrylovRitzTestsProgram,admissible_bind,
    gaussianKrylovFullMatrixProgram_admissible,fixedRitzTestsProgram_admissible,true_and]
  split <;> trivial

theorem gaussianKrylovRitzTestsProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) (j : Fin k) (ε : ℝ) :
    ∀ᵐ g ∂Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)), ∃ out,
      (gaussianKrylovRitzTestsProgram kernels T hT actions q S source G j ε g).eval = some out := by
  let M := (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).eval
  have hM : M.val.IsHermitian := by
    rw [M.property]
    exact krylovRitzFixedMatrix_isHermitian kernels T hT q _
  have hh := fixedRitzTestsProgram_success_ae kernels M.val hM j ε
  filter_upwards [hh] with g hg
  obtain ⟨tests,htests⟩ := hg
  unfold gaussianKrylovRitzTestsProgram
  rw [eval_bind,eval_bind,show (fixedRitzTestsProgram kernels
    (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).eval.val _ j ε g).eval =
      some tests from htests]
  exact ⟨_,rfl⟩

theorem gaussianKrylovRitzTestsProgram_success_of_polynomial_events
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (G : Fin r → Fin k → ℝ) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ)
    (h0 : ShiftedInertiaPolynomialGood (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix G)) 1 (g 0))
    (h1 : ShiftedInertiaPolynomialGood (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix G)) (1-2*ε) (g 1)) :
    ∃ out, (gaussianKrylovRitzTestsProgram kernels T hT actions q S source G j ε g).eval = some out := by
  let M := (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).eval
  have hM : M.val.IsHermitian := by
    rw [M.property]
    exact krylovRitzFixedMatrix_isHermitian kernels T hT q _
  have h0' : ShiftedInertiaPolynomialGood M.val 1 (g 0) := by simpa only [M.property] using h0
  have h1' : ShiftedInertiaPolynomialGood M.val (1-2*ε) (g 1) := by simpa only [M.property] using h1
  obtain ⟨tests,htests⟩ := fixedRitzTestsProgram_success_of_polynomial_events kernels M.val hM j ε g h0' h1'
  unfold gaussianKrylovRitzTestsProgram
  rw [eval_bind,eval_bind,show (fixedRitzTestsProgram kernels
    (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).eval.val _ j ε g).eval =
      some tests from htests]
  exact ⟨_,rfl⟩

def decisionOfCertifiedTests {N : ℕ} {values : Fin N → ℝ} {ε : ℝ}
    (tests : ∀ i, CertifiedRitzTests (values i) ε) : ThresholdDecision :=
  if ∃ i, (tests i).aboveOne = true then .below
  else if ∀ i, (tests i).aboveLow = false then .above else .near

theorem decisionOfCertifiedTests_eq {N : ℕ} {values : Fin N → ℝ} {ε : ℝ}
    (tests : ∀ i, CertifiedRitzTests (values i) ε) :
    decisionOfCertifiedTests tests = thresholdDecision values ε := by
  have ho : (∃ i, (tests i).aboveOne = true) ↔ ∃ i, 1 < values i :=
    exists_congr (fun i => (tests i).one_correct)
  have hl : (∀ i, (tests i).aboveLow = false) ↔ ∀ i, values i ≤ 1-2*ε := by
    apply forall_congr'
    intro i
    rw [Bool.eq_false_iff]
    exact (not_congr (tests i).low_correct).trans not_lt
  simp only [decisionOfCertifiedTests,thresholdDecision,ho,hl]
  split_ifs <;> rfl

def decisionOfOptionalTests {N : ℕ} {values : Fin N → ℝ} {ε : ℝ}
    (tests : ∀ i, Option (CertifiedRitzTests (values i) ε)) : ThresholdDecision :=
  if hn : ∃ i, tests i = none then .near
  else decisionOfCertifiedTests (fun i => (tests i).get (by
    rw [Option.isSome_iff_ne_none]
    exact fun h => hn ⟨i,h⟩))

theorem decisionOfOptionalTests_eq {N : ℕ} {values : Fin N → ℝ} {ε : ℝ}
    (tests : ∀ i, Option (CertifiedRitzTests (values i) ε))
    (hsuccess : ∀ i, ∃ out, tests i = some out) :
    decisionOfOptionalTests tests = thresholdDecision values ε := by
  have hn : ¬ ∃ i, tests i = none := by
    rintro ⟨i,hi⟩
    obtain ⟨out,ho⟩ := hsuccess i
    rw [ho] at hi
    contradiction
  simp only [decisionOfOptionalTests,dif_neg hn]
  exact decisionOfCertifiedTests_eq _

/-- Repetitions execute the full trial compiler. No native spectral value is
read by the program; it receives only certified Boolean sign tests. -/
def repeatedKrylovQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let tests ← dependentTabulate N _ (fun i =>
    gaussianKrylovRitzTestsProgram kernels T hT actions q S source (G i) j ε (g i))
  .pure (decisionOfOptionalTests tests)

theorem repeatedKrylovQueryProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    (repeatedKrylovQueryProgram kernels T hT actions q S source j ε N G g).admissible := by
  simp only [repeatedKrylovQueryProgram,admissible_bind,dependentTabulate_admissible,admissible_pure,and_true]
  exact fun i => gaussianKrylovRitzTestsProgram_admissible kernels T hT actions q S source _ j ε _

theorem repeatedKrylovQueryProgram_eq_of_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ)
    (hsuccess : ∀ i, ∃ out,
      (gaussianKrylovRitzTestsProgram kernels T hT actions q S source (G i) j ε (g i)).eval = some out) :
    (repeatedKrylovQueryProgram kernels T hT actions q S source j ε N G g).eval =
      thresholdDecision (fun i => computedKrylovRitzValue kernels T hT actions q S (G i) j) ε := by
  simp only [repeatedKrylovQueryProgram,eval_bind,dependentTabulate_eval,eval_pure]
  exact decisionOfOptionalTests_eq _ hsuccess

theorem repeatedKrylovQueryProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ) :
    (repeatedKrylovQueryProgram kernels T hT actions q S source j ε N G g).work =
      ∑ i : Fin N, (gaussianKrylovRitzTestsProgram kernels T hT actions q S source (G i) j ε (g i)).work := by
  simp only [repeatedKrylovQueryProgram,work_bind,dependentTabulate_work,work_pure,add_zero]

theorem repeatedKrylovQueryProgram_safe_of_events
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ r) (j : Fin k) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1/4) (N : ℕ)
    (G : Fin N → Fin r → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ)
    (h0 : ∀ i, ShiftedInertiaPolynomialGood
      (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix (G i))) 1 (g i 0))
    (h1 : ∀ i, ShiftedInertiaPolynomialGood
      (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix (G i))) (1-2*ε) (g i 1))
    (hritz : ∃ i, (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 ≤
      computedKrylovRitzValue kernels T hT.isHermitian actions q S (G i) j) :
    ThresholdDecisionSafe (orderedEigenvalue T hT.isHermitian j) ε
      (repeatedKrylovQueryProgram kernels T hT.isHermitian actions q S source j ε N G g).eval := by
  rw [repeatedKrylovQueryProgram_eq_of_success kernels T hT.isHermitian actions q S source j ε N G g
    (fun i => gaussianKrylovRitzTestsProgram_success_of_polynomial_events kernels T hT.isHermitian
      actions q S source (G i) j ε (g i) (h0 i) (h1 i))]
  exact thresholdDecision_safe _ _ ε (orderedEigenvalue_nonneg T hT j) hε hε'
    (fun i => computedKrylovRitzValue_always_safe kernels T hT actions q S (G i) j) hritz

end
end HierarchicalAbsoluteSpectral
