import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixBounds
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearchJitter
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftProgram
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftInertia

/-!
The original appendix's full support-level arithmetic program: exact
coefficient initialization, capped shifted-inertia search, fresh scalar
jitter, random congruence and recursive LDL, and the physical dual lift.
Both optional failures remain explicit until the final original-input
wrapper supplies its finite fallback.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator

structure ExactGramAppendixApproximation {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) (r : ℕ) (ε : ℝ) where
  result : FixedRankOutput n p r
  error : ‖A*B-result.product‖ ≤ (1+ε)*tailSingularValue (A*B) r

abbrev ExactGramAppendixTape (k : ℕ) (ε : ℝ) (hε : 0 < ε) :=
  ExactGramAppendixSearchTape k ε hε × ℝ × (Fin (k*k) → ℝ)

def exactGramAppendixCoreProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape support.dimension ε hε) :
    ArithmeticProgram (Option (ExactGramAppendixApproximation A B r ε)) :=
  if hfull : support.dimension ≤ r then do
    let result ← certify (support.exactOutputProgram kernels r hfull)
    have herr : ‖A*B-result.val.product‖ ≤ (1+ε)*tailSingularValue (A*B) r := by
      rw [result.property, support.exactOutputProgram_exact kernels r hfull, sub_self, norm_zero]
      exact mul_nonneg (by linarith) (tailSingularValue_nonneg _ _)
    ArithmeticProgram.pure (some ⟨result.val,herr⟩)
  else do
    have hr : r < support.dimension := Nat.lt_of_not_ge hfull
    let j : Fin support.dimension := ⟨r,hr⟩
    let upper ← certify (exactGramAppendixUpperProgram kernels support.core
      support.positive.posSemidef j ε hε tape.1)
    match hupper : upper.val with
    | none => ArithmeticProgram.pure none
    | some u => do
      have hu := exactGramAppendixUpperProgram_correct kernels support.core
        support.positive.posSemidef j ε hε tape.1 u (upper.property.symm.trans hupper)
      have hu0 : 0 < u := (support.eigenvalue_pos j).trans_le hu.1
      let time ← certify (exactGramAppendixJitterProgram u ε tape.2.1)
      have htime := exactGramAppendixJitterProgram_bounds u ε tape.2.1 hu0.le hε.le
      have htlo : u ≤ time.val := by simpa only [time.property] using htime.1
      have hthi : time.val ≤ (1+ε)*u := by simpa only [time.property] using htime.2
      have ht : 0 ≤ time.val := hu0.le.trans htlo
      let scaled ← certify (blockScaleProgram time.val (1 : Core support.dimension))
      let K ← certify (blockSubProgram scaled.val support.core)
      have hK : K.val = time.val • (1 : Core support.dimension)-support.core := by
        rw [K.property, blockSubProgram_eval, scaled.property, blockScaleProgram_eval]
      have hKsym : K.valᵀ = K.val := by
        rw [hK]
        have hcore : support.coreᵀ = support.core := by
          simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using support.positive.isHermitian.eq
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hcore]
      let diag? ← congruenceInertiaProgram kernels K.val hKsym
        (gaussianSquareMatrix support.dimension tape.2.2)
      match diag? with
      | none => ArithmeticProgram.pure none
      | some diag => do
        let shifted : FiniteCongruenceDiagonal
            (time.val • (1 : Core support.dimension)-support.core) := hK ▸ diag
        have hnegative : shifted.negativeCount ≤ r :=
          exactGramAppendixLift_negativeCount_le support.core support.positive.isHermitian
            time.val shifted r hr (hu.1.trans htlo)
        let result ← certify (exactGramAppendixLiftProgram kernels A B support.lift shifted hnegative)
        have herr : ‖A*B-result.val.product‖ ≤ Real.sqrt time.val := by
          rw [result.property]
          exact exactGramAppendixLiftProgram_error kernels A B support.lift support.core
            time.val ht support.orthogonal support.covariance shifted hnegative
        have hsqrt : Real.sqrt time.val ≤ (1+ε)*tailSingularValue (A*B) r := by
          exact exactGramAppendix_sqrt_budget
            (orderedEigenvalue support.core support.positive.isHermitian j)
            (tailSingularValue (A*B) r) u time.val ε (tailSingularValue_nonneg _ _)
            hε.le (support.eigenvalue_eq_sq_tail j) hu.2 hthi
        ArithmeticProgram.pure (some ⟨result.val,herr.trans hsqrt⟩)

theorem exactGramAppendixCoreProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape support.dimension ε hε) :
    (exactGramAppendixCoreProgram kernels support r ε hε tape).admissible := by
  unfold exactGramAppendixCoreProgram
  split
  · simp only [admissible_bind, certify_admissible, ExactGramAppendixSupport.exactOutputProgram,
      supportExactOutputProgram_admissible, admissible_pure, and_self]
  · simp only [admissible_bind, certify_admissible,
      exactGramAppendixUpperProgram_admissible, true_and]
    split
    · trivial
    · simp only [admissible_bind, certify_admissible, exactGramAppendixJitterProgram_admissible,
        blockScaleProgram_admissible, blockSubProgram_admissible,
        congruenceInertiaProgram_admissible, true_and]
      split
      · trivial
      · simp only [admissible_bind, certify_admissible, exactGramAppendixLiftProgram_admissible,
          admissible_pure, and_self]

theorem exactGramAppendixCoreProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape support.dimension ε hε)
    (out : ExactGramAppendixApproximation A B r ε)
    (_hout : (exactGramAppendixCoreProgram kernels support r ε hε tape).eval = some out) :
    ‖A*B-out.result.product‖ ≤ (1+ε)*tailSingularValue (A*B) r := out.error

end
end HierarchicalAbsoluteSpectral
