import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixProgram

/-! The manuscript's literal tolerance theta/100 is computed by a counted
field division before the original-input comparator is executed. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator

def exactGramAppendixAccuracyTransport
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε)
    (computed : {accuracy : ℝ // accuracy = ε}) : ArithmeticProgram (FixedRankOutput n p r) := by
  rcases computed with ⟨accuracy,haccuracy⟩
  cases haccuracy
  exact exactGramAppendixProgram kernels A B r ε hε tape

@[simp] theorem exactGramAppendixAccuracyTransport_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε)
    (computed : {accuracy : ℝ // accuracy = ε}) :
    exactGramAppendixAccuracyTransport kernels A B r ε hε tape computed =
      exactGramAppendixProgram kernels A B r ε hε tape := by
  rcases computed with ⟨accuracy,haccuracy⟩
  cases haccuracy
  rfl

abbrev ExactGramAppendixThetaTape
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (θ : ℝ) (hθ : 0 < θ) :=
  ExactGramAppendixOriginalTape kernels A B (θ/100) (div_pos hθ (by norm_num))

def exactGramAppendixThetaLaw
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (θ : ℝ) (hθ : 0 < θ) : Measure (ExactGramAppendixThetaTape kernels A B θ hθ) :=
  exactGramAppendixOriginalLaw kernels A B (θ/100) (div_pos hθ (by norm_num))

def exactGramAppendixThetaProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let accuracy ← certify (ArithmeticProgram.div θ 100)
  exactGramAppendixAccuracyTransport kernels A B r (θ/100) (div_pos hθ (by norm_num)) tape accuracy

@[simp] theorem exactGramAppendixThetaProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval =
      (exactGramAppendixProgram kernels A B r (θ/100) (div_pos hθ (by norm_num)) tape).eval := by
  simp only [exactGramAppendixThetaProgram, eval_bind, exactGramAppendixAccuracyTransport_eq]

theorem exactGramAppendixThetaProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    (exactGramAppendixThetaProgram kernels A B r θ hθ tape).admissible := by
  simp only [exactGramAppendixThetaProgram, admissible_bind, certify_admissible,
    admissible_div, exactGramAppendixAccuracyTransport_eq, exactGramAppendixProgram_admissible,
    and_true]
  norm_num

theorem exactGramAppendixThetaProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    (exactGramAppendixThetaProgram kernels A B r θ hθ tape).work =
      1+(exactGramAppendixProgram kernels A B r (θ/100) (div_pos hθ (by norm_num)) tape).work := by
  simp only [exactGramAppendixThetaProgram, work_bind, certify_work, work_div,
    exactGramAppendixAccuracyTransport_eq]

theorem exactGramAppendixThetaProgram_width
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) :
    (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width ≤ r :=
  (exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.width_le

theorem exactGramAppendixThetaProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    (exactGramAppendixThetaLaw kernels A B θ hθ)
      {tape | ‖A*B-(exactGramAppendixThetaProgram kernels A B r θ hθ tape).eval.product‖ ≤
        (1+θ/100)*tailSingularValue (A*B) r} = 1 := by
  simp only [exactGramAppendixThetaProgram_eval, exactGramAppendixThetaLaw]
  exact exactGramAppendixProgram_error_probability kernels A B r (θ/100) (div_pos hθ (by norm_num))

def exactGramAppendixThetaGaussianDraws
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (θ : ℝ) (hθ : 0 < θ) : ℕ :=
  let k := (exactGramAppendixCanonicalSupport kernels A B).dimension
  exactGramAppendixSearchGaussianDraws k (θ/100) (div_pos hθ (by norm_num))+1+k*k

theorem exactGramAppendixThetaGaussianDraws_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (θ : ℝ) (hθ : 0 < θ) :
    exactGramAppendixThetaGaussianDraws kernels A B θ hθ ≤
      exactGramAppendixSearchCap m (θ/100) (div_pos hθ (by norm_num))*(m*m)+1+m*m :=
  exactGramAppendix_draws_le _ m (exactGramAppendixCanonicalSupport kernels A B).dimension_le _ _

def exactGramAppendixTotalWork
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (θ : ℝ) (hθ : 0 < θ) (tape : ExactGramAppendixThetaTape kernels A B θ hθ) : ℕ :=
  (exactGramAppendixThetaProgram kernels A B r θ hθ tape).work+
    exactGramAppendixThetaGaussianDraws kernels A B θ hθ+n*p+m*(n+p)

end
end HierarchicalAbsoluteSpectral
