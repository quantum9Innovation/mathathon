import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixProbability
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSupportCost

/-!
The original-input Gram comparator. Preprocessing is executed once, then
the finite Gaussian tape is transported to its proved product-support
dimension. Failed zero checks return the width-zero output. Such failures
have probability zero, and every outcome returns explicit matrix factors
and the dense product within the finite operation budget.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator

def exactGramAppendixCanonicalSupport
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    ExactGramAppendixSupport A B := (exactGramAppendixSupportProgram kernels A B).eval

abbrev ExactGramAppendixOriginalTape
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (ε : ℝ) (hε : 0 < ε) :=
  ExactGramAppendixTape (exactGramAppendixCanonicalSupport kernels A B).dimension ε hε

def exactGramAppendixOriginalLaw
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (ε : ℝ) (hε : 0 < ε) : Measure (ExactGramAppendixOriginalTape kernels A B ε hε) :=
  exactGramAppendixLaw (exactGramAppendixCanonicalSupport kernels A B).dimension ε hε

instance exactGramAppendixOriginalLaw_isProbability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (ε : ℝ) (hε : 0 < ε) : IsProbabilityMeasure (exactGramAppendixOriginalLaw kernels A B ε hε) := by
  unfold exactGramAppendixOriginalLaw
  infer_instance

def exactGramAppendixTransportProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (canonical : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape canonical.dimension ε hε)
    (computed : {support : ExactGramAppendixSupport A B // support = canonical}) :
    ArithmeticProgram (Option (ExactGramAppendixApproximation A B r ε)) := by
  rcases computed with ⟨support,hsupport⟩
  cases hsupport
  exact exactGramAppendixCoreProgram kernels canonical r ε hε tape

@[simp] theorem exactGramAppendixTransportProgram_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (canonical : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape canonical.dimension ε hε)
    (computed : {support : ExactGramAppendixSupport A B // support = canonical}) :
    exactGramAppendixTransportProgram kernels canonical r ε hε tape computed =
      exactGramAppendixCoreProgram kernels canonical r ε hε tape := by
  rcases computed with ⟨support,hsupport⟩
  cases hsupport
  rfl

def exactGramAppendixOptionalProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    ArithmeticProgram (Option (ExactGramAppendixApproximation A B r ε)) := do
  let support ← certify (exactGramAppendixSupportProgram kernels A B)
  exactGramAppendixTransportProgram kernels (exactGramAppendixCanonicalSupport kernels A B)
    r ε hε tape support

@[simp] theorem exactGramAppendixOptionalProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    (exactGramAppendixOptionalProgram kernels A B r ε hε tape).eval =
      (exactGramAppendixCoreProgram kernels (exactGramAppendixCanonicalSupport kernels A B)
        r ε hε tape).eval := by
  simp only [exactGramAppendixOptionalProgram, eval_bind, exactGramAppendixTransportProgram_eq]

theorem exactGramAppendixOptionalProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    (exactGramAppendixOptionalProgram kernels A B r ε hε tape).work =
      (exactGramAppendixSupportProgram kernels A B).work+
        (exactGramAppendixCoreProgram kernels (exactGramAppendixCanonicalSupport kernels A B)
          r ε hε tape).work := by
  simp only [exactGramAppendixOptionalProgram, work_bind, certify_work,
    exactGramAppendixTransportProgram_eq]

def exactGramAppendixProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let out? ← exactGramAppendixOptionalProgram kernels A B r ε hε tape
  ArithmeticProgram.pure (match out? with
    | none => zeroFixedRankOutput n p r
    | some out => out.result)

theorem exactGramAppendixProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    (exactGramAppendixProgram kernels A B r ε hε tape).admissible := by
  simp only [exactGramAppendixProgram, admissible_bind, admissible_pure,
    exactGramAppendixOptionalProgram, certify_admissible, exactGramAppendixTransportProgram_eq,
    exactGramAppendixSupportProgram_admissible, exactGramAppendixCoreProgram_admissible, and_self]

theorem exactGramAppendixProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (tape : ExactGramAppendixOriginalTape kernels A B ε hε) :
    (exactGramAppendixProgram kernels A B r ε hε tape).work =
      (exactGramAppendixSupportProgram kernels A B).work+
        (exactGramAppendixCoreProgram kernels (exactGramAppendixCanonicalSupport kernels A B)
          r ε hε tape).work := by
  simp only [exactGramAppendixProgram, work_bind, work_pure, add_zero,
    exactGramAppendixOptionalProgram_work]

theorem exactGramAppendixProgram_error_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ tape ∂exactGramAppendixOriginalLaw kernels A B ε hε,
      ‖A*B-(exactGramAppendixProgram kernels A B r ε hε tape).eval.product‖ ≤
        (1+ε)*tailSingularValue (A*B) r := by
  filter_upwards [exactGramAppendixCoreProgram_success_ae kernels
    (exactGramAppendixCanonicalSupport kernels A B) r ε hε] with tape hsuccess
  obtain ⟨out,hout⟩ := hsuccess
  simp only [exactGramAppendixProgram, eval_bind, exactGramAppendixOptionalProgram_eval, hout, eval_pure]
  exact out.error

/-- A probability-one spectral-error guarantee for the original matrices,
with explicit factors, explicit dense output, and width at most r on
every outcome. No successful-certificate hypothesis occurs here. -/
theorem exactGramAppendixProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (exactGramAppendixOriginalLaw kernels A B ε hε)
      {tape | ‖A*B-(exactGramAppendixProgram kernels A B r ε hε tape).eval.product‖ ≤
        (1+ε)*tailSingularValue (A*B) r} = 1 := by
  apply le_antisymm
  · calc
      _ ≤ (exactGramAppendixOriginalLaw kernels A B ε hε) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · calc
      1 = (exactGramAppendixOriginalLaw kernels A B ε hε) Set.univ := by simp
      _ ≤ _ := measure_mono_ae (by
        filter_upwards [exactGramAppendixProgram_error_ae kernels A B r ε hε] with tape htape
        exact fun _ => htape)

end
end HierarchicalAbsoluteSpectral
