import HierarchicalAbsoluteSpectral.ExactGramCharpolyBranchingProgram
import HierarchicalAbsoluteSpectral.ExactGramCharpolyCompanionForm
import HierarchicalAbsoluteSpectral.ExactGramCharpolyProductCompanion
import HierarchicalAbsoluteSpectral.ExactGramCharpolyInitializer

/-!
An actual deterministic exact-field characteristic-polynomial algorithm.
The program executes logarithmically many compressed Krylov doublings,
computes the conjugated matrix with two verified matrix products, extracts
its companion last columns, and multiplies their coefficient arrays.
No characteristic-polynomial, root, sign-count, or spectral oracle is an
input to this construction.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped BigOperators

structure ExactGramCharpolyData {n : ℕ} (A : Core n) where
  coefficients : ExactGramDensePolynomial n ℝ
  correct : exactGramDenseToPolynomial coefficients = A.charpoly

def exactGramRawChainCoefficients {n d : ℕ} {A : Core n}
    (b : ExactGramKrylovBasis A d) (chain : ExactGramChainIndexData b.labels)
    (H : Core b.width) (g : Fin n) : Fin (chain.length g) → ℝ :=
  fun r => exactGramIndexedBlock H b.generator chain.length chain.index g r
    ⟨chain.length g-1, by have hr := r.isLt; omega⟩

def exactGramCharpolyFromBasisProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) (hnd : n ≤ d) :
    ArithmeticProgram (ExactGramCharpolyData A) := do
  let H₁ ← certify (rankProfileMulProgram kernels b.inverse A)
  let H ← certify (rankProfileMulProgram kernels H₁.val b.basis)
  have hH : H.val = b.frobenius := by
    rw [H.property, rankProfileMulProgram_eval, H₁.property, rankProfileMulProgram_eval]
    rfl
  let chain := b.chains hnd
  let c := exactGramRawChainCoefficients b chain H.val
  have hc : c = b.chainCoefficients chain := by
    funext g r
    dsimp only [c, exactGramRawChainCoefficients]
    rw [hH]
    rfl
  let values ← certify (exactGramCompanionProductProgram chain.length c)
  have hcorrect : exactGramDenseToPolynomial values.val = A.charpoly := by
    rw [values.property, exactGramCompanionProductProgram_eval, hc]
    exact (b.charpoly_eq_chain_product hnd chain).symm
  let hdegree : (∑ g, chain.length g) = n := chain.sum_length.trans b.width_eq
  ArithmeticProgram.pure {
    coefficients := exactGramDenseCast hdegree values.val
    correct := by rw [exactGramDenseToPolynomial_cast]; exact hcorrect }

theorem exactGramCharpolyFromBasisProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) (hnd : n ≤ d) :
    (exactGramCharpolyFromBasisProgram kernels b hnd).admissible := by
  simp only [exactGramCharpolyFromBasisProgram, admissible_bind, certify_admissible,
    rankProfileMulProgram_admissible, exactGramCompanionProductProgram_admissible,
    admissible_pure, and_self]

theorem exactGramCharpolyFromBasisProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n d : ℕ} {A : Core n} (b : ExactGramKrylovBasis A d) (hnd : n ≤ d) :
    (exactGramCharpolyFromBasisProgram kernels b hnd).rankProfileFieldOnly := by
  simp only [exactGramCharpolyFromBasisProgram, rankProfileFieldOnly_bind,
    rankProfileFieldOnly_certify, rankProfileMulProgram_fieldOnly,
    exactGramCompanionProductProgram_fieldOnly, rankProfileFieldOnly_pure, and_self]

def exactGramCharpolyProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) : ArithmeticProgram (ExactGramCharpolyData A) := do
  let b ← exactGramBranchingProgram kernels A (Nat.clog 2 (n+1))
  have hnd : n ≤ exactGramKrylovWidth (Nat.clog 2 (n+1)) := by
    rw [exactGramKrylovWidth_eq]
    exact (Nat.le_succ n).trans (Nat.le_pow_clog (by norm_num) _)
  exactGramCharpolyFromBasisProgram kernels b hnd

theorem exactGramCharpolyProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) :
    exactGramDenseToPolynomial (exactGramCharpolyProgram kernels A).eval.coefficients = A.charpoly :=
  (exactGramCharpolyProgram kernels A).eval.correct

theorem exactGramCharpolyProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) : (exactGramCharpolyProgram kernels A).admissible := by
  simp only [exactGramCharpolyProgram, admissible_bind, exactGramBranchingProgram_admissible,
    exactGramCharpolyFromBasisProgram_admissible, and_self]

theorem exactGramCharpolyProgram_fieldOnly
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) : (exactGramCharpolyProgram kernels A).rankProfileFieldOnly := by
  simp only [exactGramCharpolyProgram, rankProfileFieldOnly_bind, exactGramBranchingProgram_fieldOnly,
    exactGramCharpolyFromBasisProgram_fieldOnly, and_self]

/-- The original coefficient-ratio initializer, now called on coefficients
computed by the exact-field algorithm above. -/
def exactGramCharpolyInitializerProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (j : Fin n) (stretch : ℝ) : ArithmeticProgram InitializerResult := do
  let out ← exactGramCharpolyProgram kernels A
  exactGramCoeffInitializerProgram (exactGramDenseToPolynomial out.coefficients) j stretch

@[simp] theorem exactGramCharpolyInitializerProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (j : Fin n) (stretch : ℝ) :
    (exactGramCharpolyInitializerProgram kernels A j stretch).eval =
      (exactGramCoeffInitializerProgram A.charpoly j stretch).eval := by
  simp only [exactGramCharpolyInitializerProgram, eval_bind, exactGramCharpolyProgram_correct]

theorem exactGramCharpolyInitializerProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (hA : A.PosSemidef) (j : Fin n) (stretch : ℝ)
    (hstretch : 0 < stretch) :
    (exactGramCharpolyInitializerProgram kernels A j stretch).admissible := by
  simp only [exactGramCharpolyInitializerProgram, admissible_bind,
    exactGramCharpolyProgram_admissible, exactGramCharpolyProgram_correct, true_and]
  exact exactGramCoeffInitializerProgram_admissible A hA j stretch hstretch

theorem exactGramCharpolyInitializerProgram_work_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (j : Fin n) (stretch : ℝ) :
    (exactGramCharpolyInitializerProgram kernels A j stretch).work ≤
      (exactGramCharpolyProgram kernels A).work+7 := by
  simp only [exactGramCharpolyInitializerProgram, work_bind]
  exact Nat.add_le_add_left (exactGramCoeffInitializerProgram_work_le _ _ _) _

theorem exactGramCharpolyInitializerProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} (A : Core n) (hA : A.PosSemidef) (j : Fin n) (stretch target : ℝ)
    (hstretch : 1 ≤ stretch)
    (hcompare : orderedEigenvalue A hA.isHermitian j / stretch ≤ target ∧
      target ≤ stretch * orderedEigenvalue A hA.isHermitian j) :
    match (exactGramCharpolyInitializerProgram kernels A j stretch).eval with
    | .exact => target = 0
    | .bracket lower upper => 0 < lower ∧ lower ≤ target ∧ target ≤ upper ∧
        upper/lower = (stretch*n)^2 := by
  rw [exactGramCharpolyInitializerProgram_eval]
  exact exactGramCoeffInitializerProgram_correct A hA j stretch target hstretch hcompare

end
end HierarchicalAbsoluteSpectral
