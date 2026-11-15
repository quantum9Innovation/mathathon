import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSearch

/-! Almost-everywhere success of finite exact bisection.  The proof uses
the finite binary tree of deterministic candidate intervals; it never
assumes one event succeeds simultaneously at every real threshold. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix MeasureTheory
open ArithmeticProgram hiding pure

theorem exactGramAppendixSearchIndexed_success_ae
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {cap : ℕ} (query : Fin cap → ℝ → Ω → ArithmeticProgram (Option Bool))
    (hquery : ∀ i t, ∀ᵐ x ∂μ, ∃ b, (query i t x).eval = some b)
    (ε : ℝ) (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ) :
    ∀ᵐ g ∂Measure.pi (fun _ : Fin cap => μ), ∃ out,
      (exactGramAppendixSearchIndexed (fun i t => query i t (g i))
        ε fuel offset hcap l u).eval = some out := by
  simp only [exactGramAppendixSearchIndexed_eval]
  induction fuel generalizing offset l u with
  | zero => exact Filter.Eventually.of_forall (fun _ => ⟨.bracket l u, rfl⟩)
  | succ fuel ih =>
      by_cases hstop : u-l ≤ ε*l
      · exact Filter.Eventually.of_forall (fun _ =>
          ⟨.bracket l u, by simp only [exactGramAppendixSearchIndexedValue, if_pos hstop]⟩)
      · let i : Fin cap := ⟨offset, by omega⟩
        let t := (l+u)/2
        have hroot : ∀ᵐ g ∂Measure.pi (fun _ : Fin cap => μ),
            ∃ b, (query i t (g i)).eval = some b :=
          (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin cap => μ) (i := i)).eventually
            (hquery i t)
        have hleft := ih (offset+1) (by omega) t u
        have hright := ih (offset+1) (by omega) l t
        filter_upwards [hroot, hleft, hright] with g hg hgl hgr
        obtain ⟨b, hb⟩ := hg
        cases b with
        | false =>
            simpa only [exactGramAppendixSearchIndexedValue, if_neg hstop, hb] using hgr
        | true =>
            simpa only [exactGramAppendixSearchIndexedValue, if_neg hstop, hb] using hgl

variable {n : ℕ}

theorem exactGramAppendixEigenvalueQuery_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (j : Fin n) (t : ℝ) :
    ∀ᵐ g ∂gaussianVector (n*n), ∃ b,
      (exactGramAppendixEigenvalueQuery kernels A hA j g t).eval = some b := by
  filter_upwards [shiftedSingularEigenvalueTestProgram_success_ae kernels A hA t j] with g hg
  obtain ⟨out, hout⟩ := hg
  refine ⟨out.answer, ?_⟩
  simp only [exactGramAppendixEigenvalueQuery, eval_bind, hout, eval_pure, Option.map_some]

theorem exactGramAppendixSearchProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ g ∂exactGramAppendixSearchLaw n ε hε, ∃ out,
      (exactGramAppendixSearchProgram kernels A hA j ε hε g).eval = some out := by
  cases hinitial : (exactGramCharpolyInitializerProgram kernels A j 1).eval with
  | exact =>
      exact Filter.Eventually.of_forall (fun g => ⟨.exact, by
        rw [exactGramAppendixSearchProgram_eval, hinitial]⟩)
  | bracket l u =>
      have h := exactGramAppendixSearchIndexed_success_ae (gaussianVector (n*n))
        (fun (_ : Fin (exactGramAppendixSearchCap n ε hε)) t g =>
          exactGramAppendixEigenvalueQuery kernels A hA.isHermitian j g t)
        (fun _ t => exactGramAppendixEigenvalueQuery_success_ae kernels A hA.isHermitian j t)
        ε (exactGramAppendixSearchCap n ε hε) 0 (by omega) l u
      filter_upwards [h] with g hg
      simpa only [exactGramAppendixSearchProgram_eval, hinitial] using hg

theorem exactGramAppendixUpperProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ g ∂exactGramAppendixSearchLaw n ε hε, ∃ u,
      (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u ∧
      orderedEigenvalue A hA.isHermitian j ≤ u ∧
      u ≤ (1+ε)*orderedEigenvalue A hA.isHermitian j := by
  filter_upwards [exactGramAppendixSearchProgram_success_ae kernels A hA j ε hε] with g hg
  obtain ⟨out, hout⟩ := hg
  let u : ℝ := match out with | .exact => 0 | .bracket _ v => v
  have hu : (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u := by
    simp only [exactGramAppendixUpperProgram, eval_bind, hout, eval_pure, Option.map_some]
    rfl
  exact ⟨u, hu, exactGramAppendixUpperProgram_correct kernels A hA j ε hε g u hu⟩

end
end HierarchicalAbsoluteSpectral
