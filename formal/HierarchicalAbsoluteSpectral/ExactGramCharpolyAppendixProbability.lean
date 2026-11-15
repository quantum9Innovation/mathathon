import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixCore
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearchGaussian
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRandom

/-!
Probability-one completion of the literal Gram comparator. Exact bisection
has one deterministic successful endpoint. This permits an ordinary
independent product law for that search, the fresh scalar jitter, and the
fresh square Gaussian congruence, without an all-threshold success event.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open ArithmeticProgram hiding pure

private theorem appendix_certify_eval_eq {α : Type} (p : ArithmeticProgram α) :
    (certify p).eval = ⟨p.eval,rfl⟩ := Subtype.ext (certify_eval p)

def exactGramAppendixLaw (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Measure (ExactGramAppendixTape k ε hε) :=
  (exactGramAppendixSearchLaw k ε hε).prod
    ((gaussianReal 0 1).prod (gaussianVector (k*k)))

instance exactGramAppendixLaw_isProbability (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (exactGramAppendixLaw k ε hε) := by
  unfold exactGramAppendixLaw
  infer_instance

theorem exactGramAppendixCoreProgram_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tape : ExactGramAppendixTape support.dimension ε hε) (hr : r < support.dimension)
    (u : ℝ)
    (hupper : (exactGramAppendixUpperProgram kernels support.core support.positive.posSemidef
      ⟨r,hr⟩ ε hε tape.1).eval = some u)
    (hdiag : ∃ out, (congruenceInertiaProgram kernels
      ((exactGramAppendixJitterProgram u ε tape.2.1).eval • (1 : Core support.dimension)-support.core)
      (by
        have hsym : support.coreᵀ = support.core := by
          simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using support.positive.isHermitian.eq
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsym])
      (gaussianSquareMatrix support.dimension tape.2.2)).eval = some out) :
    ∃ out, (exactGramAppendixCoreProgram kernels support r ε hε tape).eval = some out := by
  have hfull : ¬support.dimension ≤ r := by omega
  obtain ⟨diag,hdiag⟩ := hdiag
  have hcert : (certify (exactGramAppendixUpperProgram kernels support.core
      support.positive.posSemidef ⟨r,hr⟩ ε hε tape.1)).eval =
      ⟨some u,hupper.symm⟩ := by
    apply Subtype.ext
    exact (certify_eval _).trans hupper
  let time := (exactGramAppendixJitterProgram u ε tape.2.1).eval
  have htime : (certify (exactGramAppendixJitterProgram u ε tape.2.1)).eval =
      ⟨time,rfl⟩ := appendix_certify_eval_eq _
  have hscaled : (certify (blockScaleProgram time (1 : Core support.dimension))).eval =
      ⟨time • (1 : Core support.dimension), (blockScaleProgram_eval _ _).symm⟩ := by
    apply Subtype.ext
    exact (certify_eval _).trans (blockScaleProgram_eval _ _)
  have hmatrix : (certify (blockSubProgram (time • (1 : Core support.dimension)) support.core)).eval =
      ⟨time • (1 : Core support.dimension)-support.core, (blockSubProgram_eval _ _).symm⟩ := by
    apply Subtype.ext
    exact (certify_eval _).trans (blockSubProgram_eval _ _)
  unfold exactGramAppendixCoreProgram
  rw [dif_neg hfull, eval_bind, hcert]
  rw [eval_bind, htime, eval_bind, hscaled, eval_bind, hmatrix, eval_bind, hdiag]
  simp only [eval_bind, eval_pure]
  exact ⟨_,rfl⟩

theorem exactGramAppendixCoreProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}
    (support : ExactGramAppendixSupport A B) (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ tape ∂exactGramAppendixLaw support.dimension ε hε,
      ∃ out, (exactGramAppendixCoreProgram kernels support r ε hε tape).eval = some out := by
  by_cases hfull : support.dimension ≤ r
  · exact Filter.Eventually.of_forall (fun tape => by
      simp only [exactGramAppendixCoreProgram, dif_pos hfull, eval_bind, eval_pure]
      exact ⟨_,rfl⟩)
  · have hr : r < support.dimension := Nat.lt_of_not_ge hfull
    let j : Fin support.dimension := ⟨r,hr⟩
    obtain ⟨uIdeal,hu,hunique,hsuccess⟩ := exactGramAppendixUpperProgram_fixed_output kernels
      support.core support.positive.posSemidef j ε hε
    have hu0 : 0 < uIdeal := (support.eigenvalue_pos j).trans_le hu.1
    let time : ℝ → ℝ := fun g => (exactGramAppendixJitterProgram uIdeal ε g).eval
    have hTime : Continuous time := exactGramAppendixJitterProgram_continuous uIdeal ε
    have hdet : ∀ᵐ g ∂gaussianReal 0 1,
        IsUnit (time g • (1 : Core support.dimension)-support.core).det := by
      filter_upwards [exactGramAppendixJitterProgram_nonsingular_ae support.core
        support.positive.isHermitian uIdeal hu0 ε hε] with g hg
      exact isUnit_iff_ne_zero.mpr hg
    have hcongruence := exactGramAppendixLift_jointCongruence_success_ae kernels
      support.core support.positive.isHermitian time hTime hdet
    have hs := (measurePreserving_fst
      (μ := exactGramAppendixSearchLaw support.dimension ε hε)
      (ν := (gaussianReal 0 1).prod (gaussianVector (support.dimension*support.dimension)))).quasiMeasurePreserving.ae
      hsuccess
    have hc := (measurePreserving_snd
      (μ := exactGramAppendixSearchLaw support.dimension ε hε)
      (ν := (gaussianReal 0 1).prod (gaussianVector (support.dimension*support.dimension)))).quasiMeasurePreserving.ae
      hcongruence
    filter_upwards [hs,hc] with tape hsearch hcong
    exact exactGramAppendixCoreProgram_success kernels support r ε hε tape hr uIdeal hsearch hcong

end
end HierarchicalAbsoluteSpectral
