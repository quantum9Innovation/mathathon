import HierarchicalAbsoluteSpectral.ExactGramCharpolyCoeff
import HierarchicalAbsoluteSpectral.GaussianPolynomial
import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-! A counted scalar Gaussian jitter. Nonsingularity is proved by finite
polynomial root sets and the spectral product identity; no roots are computed. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix MeasureTheory ProbabilityTheory Polynomial
open ArithmeticProgram hiding pure
open scoped BigOperators

def exactGramAppendixJitterValue (u ε g : ℝ) : ℝ :=
  u*(1+ε*g^2/(1+g^2))

/-- With `ε=θ/100`, this is the appendix's displayed scalar jitter. -/
def exactGramAppendixJitterProgram (u ε g : ℝ) : ArithmeticProgram ℝ := do
  let square ← mul g g
  let numerator ← mul ε square
  let denominator ← add 1 square
  let ratio ← div numerator denominator
  let factor ← add 1 ratio
  mul u factor

@[simp] theorem exactGramAppendixJitterProgram_eval (u ε g : ℝ) :
    (exactGramAppendixJitterProgram u ε g).eval = exactGramAppendixJitterValue u ε g := by
  simp only [exactGramAppendixJitterProgram, eval_bind, eval_mul, eval_add, eval_div,
    exactGramAppendixJitterValue, pow_two]

@[simp] theorem exactGramAppendixJitterProgram_work (u ε g : ℝ) :
    (exactGramAppendixJitterProgram u ε g).work = 6 := by
  simp only [exactGramAppendixJitterProgram, work_bind, work_mul, work_add, work_div]

theorem exactGramAppendixJitterProgram_admissible (u ε g : ℝ) :
    (exactGramAppendixJitterProgram u ε g).admissible := by
  have hden : 0 < 1+g*g := by nlinarith [sq_nonneg g]
  simp only [exactGramAppendixJitterProgram, admissible_bind, admissible_mul,
    admissible_add, admissible_div, eval_mul, eval_add, eval_div, true_and, and_true]
  exact hden.ne'

theorem exactGramAppendixJitter_bounds (u ε g : ℝ) (hu : 0 ≤ u) (hε : 0 ≤ ε) :
    u ≤ exactGramAppendixJitterValue u ε g ∧
      exactGramAppendixJitterValue u ε g ≤ (1+ε)*u := by
  have hden : 0 < 1+g^2 := by positivity
  have hratio : 0 ≤ ε*g^2/(1+g^2) := div_nonneg (mul_nonneg hε (sq_nonneg g)) hden.le
  have hratio_le : ε*g^2/(1+g^2) ≤ ε := by
    rw [div_le_iff₀ hden]
    nlinarith
  dsimp only [exactGramAppendixJitterValue]
  constructor
  · nlinarith [mul_nonneg hu hratio]
  · nlinarith [mul_le_mul_of_nonneg_left hratio_le hu]

theorem exactGramAppendixJitterProgram_bounds (u ε g : ℝ) (hu : 0 ≤ u) (hε : 0 ≤ ε) :
    u ≤ (exactGramAppendixJitterProgram u ε g).eval ∧
      (exactGramAppendixJitterProgram u ε g).eval ≤ (1+ε)*u := by
  rw [exactGramAppendixJitterProgram_eval]
  exact exactGramAppendixJitter_bounds u ε g hu hε

theorem exactGramAppendixJitterProgram_continuous (u ε : ℝ) :
    Continuous (fun g : ℝ => (exactGramAppendixJitterProgram u ε g).eval) := by
  simp only [exactGramAppendixJitterProgram_eval, exactGramAppendixJitterValue]
  apply Continuous.mul continuous_const
  apply Continuous.add continuous_const
  apply Continuous.div
  · exact continuous_const.mul (continuous_id.pow 2)
  · exact continuous_const.add (continuous_id.pow 2)
  · intro g
    positivity

theorem exactGramAppendixJitter_strict (u ε g : ℝ)
    (hu : 0 < u) (hε : 0 < ε) (hg : g ≠ 0) :
    u < exactGramAppendixJitterValue u ε g := by
  have hratio : 0 < ε*g^2/(1+g^2) :=
    div_pos (mul_pos hε (sq_pos_of_ne_zero hg)) (by positivity)
  dsimp only [exactGramAppendixJitterValue]
  nlinarith [mul_pos hu hratio]

/-- For every fixed value, the collision equation is a nonzero quadratic
polynomial after clearing the positive denominator. -/
theorem exactGramAppendixJitter_finite_fiber (u ε a : ℝ)
    (hu : 0 < u) (hε : 0 < ε) :
    Set.Finite {g : ℝ | exactGramAppendixJitterValue u ε g = a} := by
  let p : ℝ[X] := C (u-a)+C (u*(1+ε)-a)*X^2
  have hp : p ≠ 0 := by
    intro hz
    have hzero := congrArg (Polynomial.eval 0) hz
    have hone := congrArg (Polynomial.eval 1) hz
    simp [p] at hzero hone
    nlinarith [mul_pos hu hε]
  apply (Polynomial.finite_setOf_isRoot hp).subset
  intro g hg
  have hden : 0 < 1+g^2 := by positivity
  change exactGramAppendixJitterValue u ε g = a at hg
  unfold exactGramAppendixJitterValue at hg
  field_simp [hden.ne'] at hg
  change p.IsRoot g
  simp only [Polynomial.IsRoot, p, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  nlinarith [hg]

theorem exactGramAppendixJitter_avoid_value_ae (u ε a : ℝ)
    (hu : 0 < u) (hε : 0 < ε) :
    ∀ᵐ g ∂gaussianReal 0 1, exactGramAppendixJitterValue u ε g ≠ a := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  apply ae_iff.mpr
  simpa only [not_not] using
    (exactGramAppendixJitter_finite_fiber u ε a hu hε).measure_zero (gaussianReal 0 1)

theorem exactGramAppendixJitter_strict_ae (u ε target : ℝ)
    (hu : 0 < u) (hε : 0 < ε) (htarget : target ≤ u) :
    ∀ᵐ g ∂gaussianReal 0 1, target < exactGramAppendixJitterValue u ε g := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hne : ∀ᵐ g ∂gaussianReal 0 1, g ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hne] with g hg
  exact htarget.trans_lt (exactGramAppendixJitter_strict u ε g hu hε hg)

theorem exactGramAppendixJitter_nonsingular_ae {n : ℕ}
    (A : Core n) (hA : A.IsHermitian) (u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∀ᵐ g ∂gaussianReal 0 1,
      (exactGramAppendixJitterValue u ε g • (1 : Core n)-A).det ≠ 0 := by
  have hall : ∀ᵐ g ∂gaussianReal 0 1, ∀ i : Fin n,
      exactGramAppendixJitterValue u ε g ≠ orderedEigenvalue A hA i := by
    apply ae_all_iff.mpr
    intro i
    exact exactGramAppendixJitter_avoid_value_ae u ε _ hu hε
  filter_upwards [hall] with g hg
  have hscalar : Matrix.scalar (Fin n) (exactGramAppendixJitterValue u ε g) =
      exactGramAppendixJitterValue u ε g • (1 : Core n) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [← hscalar, ← Matrix.eval_charpoly, exactGram_charpoly_eq_prod A hA]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hg i))

theorem exactGramAppendixJitterProgram_nonsingular_ae {n : ℕ}
    (A : Core n) (hA : A.IsHermitian) (u : ℝ) (hu : 0 < u) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ g ∂gaussianReal 0 1,
      ((exactGramAppendixJitterProgram u ε g).eval • (1 : Core n)-A).det ≠ 0 := by
  simpa only [exactGramAppendixJitterProgram_eval] using
    exactGramAppendixJitter_nonsingular_ae A hA u ε hu hε

/-- The exact output of the six-operation program is a valid upward,
nonsingular perturbation on a full-measure scalar Gaussian event. -/
theorem exactGramAppendixJitterProgram_good_ae {n : ℕ}
    (A : Core n) (hA : A.IsHermitian) (u ε target : ℝ)
    (hu : 0 < u) (hε : 0 < ε) (htarget : target ≤ u) :
    ∀ᵐ g ∂gaussianReal 0 1,
      u ≤ (exactGramAppendixJitterProgram u ε g).eval ∧
      (exactGramAppendixJitterProgram u ε g).eval ≤ (1+ε)*u ∧
      target < (exactGramAppendixJitterProgram u ε g).eval ∧
      ((exactGramAppendixJitterProgram u ε g).eval • (1 : Core n)-A).det ≠ 0 := by
  filter_upwards [exactGramAppendixJitter_strict_ae u ε target hu hε htarget,
    exactGramAppendixJitter_nonsingular_ae A hA u ε hu hε] with g hstrict hdet
  rw [exactGramAppendixJitterProgram_eval]
  exact ⟨(exactGramAppendixJitter_bounds u ε g hu.le hε.le).1,
    (exactGramAppendixJitter_bounds u ε g hu.le hε.le).2, hstrict, hdet⟩

end
end HierarchicalAbsoluteSpectral
