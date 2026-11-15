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

/-- Exact comparisons make every successful traversal of the bisection
tree identical, even when the two optional query implementations differ. -/
theorem exactGramAppendixSearchIndexedValue_some_unique
    {cap : ℕ} (query₁ query₂ : Fin cap → ℝ → Option Bool) (target ε : ℝ)
    (hsound₁ : ∀ i t b, query₁ i t = some b → (b = true ↔ t < target))
    (hsound₂ : ∀ i t b, query₂ i t = some b → (b = true ↔ t < target))
    (fuel offset : ℕ) (hcap : offset+fuel ≤ cap) (l u : ℝ)
    (out₁ out₂ : InitializerResult)
    (h₁ : exactGramAppendixSearchIndexedValue query₁ ε fuel offset hcap l u = some out₁)
    (h₂ : exactGramAppendixSearchIndexedValue query₂ ε fuel offset hcap l u = some out₂) :
    out₁ = out₂ := by
  induction fuel generalizing offset l u with
  | zero => exact Option.some.inj (h₁.symm.trans h₂)
  | succ fuel ih =>
      rw [exactGramAppendixSearchIndexedValue] at h₁ h₂
      by_cases hstop : u-l ≤ ε*l
      · rw [if_pos hstop] at h₁ h₂
        exact Option.some.inj (h₁.symm.trans h₂)
      · rw [if_neg hstop] at h₁ h₂
        let i : Fin cap := ⟨offset, by omega⟩
        let t := (l+u)/2
        change (match query₁ i t with
          | none => none
          | some true => exactGramAppendixSearchIndexedValue query₁ ε fuel (offset+1) (by omega) t u
          | some false => exactGramAppendixSearchIndexedValue query₁ ε fuel (offset+1) (by omega) l t)
            = some out₁ at h₁
        change (match query₂ i t with
          | none => none
          | some true => exactGramAppendixSearchIndexedValue query₂ ε fuel (offset+1) (by omega) t u
          | some false => exactGramAppendixSearchIndexedValue query₂ ε fuel (offset+1) (by omega) l t)
            = some out₂ at h₂
        cases hq₁ : query₁ i t with
        | none => simp only [hq₁] at h₁; cases h₁
        | some b₁ =>
            cases hq₂ : query₂ i t with
            | none => simp only [hq₂] at h₂; cases h₂
            | some b₂ =>
                have hs₁ := hsound₁ i t b₁ hq₁
                have hs₂ := hsound₂ i t b₂ hq₂
                have hb : b₁ = b₂ := Bool.eq_iff_iff.mpr (hs₁.trans hs₂.symm)
                subst b₂
                cases b₁ with
                | false =>
                    simp only [hq₁, hq₂] at h₁ h₂
                    exact ih (offset+1) (by omega) l t h₁ h₂
                | true =>
                    simp only [hq₁, hq₂] at h₁ h₂
                    exact ih (offset+1) (by omega) t u h₁ h₂

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
        dsimp only [i, t] at hb hgl hgr
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
  simp only [exactGramAppendixEigenvalueQuery, eval_bind,
    exactGramAppendixShiftedEigenvalueTestProgram_eval, hout, eval_pure, Option.map_some]

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
  let upper : InitializerResult → ℝ := fun result =>
    match result with | .exact => 0 | .bracket _ v => v
  let u := upper out
  have hu : (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u := by
    simp only [exactGramAppendixUpperProgram, eval_bind, hout, eval_pure, Option.map_some]
    rfl
  exact ⟨u, hu, exactGramAppendixUpperProgram_correct kernels A hA j ε hε g u hu⟩

theorem exactGramAppendixSearchProgram_some_unique
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g₁ g₂ : ExactGramAppendixSearchTape n ε hε) (out₁ out₂ : InitializerResult)
    (h₁ : (exactGramAppendixSearchProgram kernels A hA j ε hε g₁).eval = some out₁)
    (h₂ : (exactGramAppendixSearchProgram kernels A hA j ε hε g₂).eval = some out₂) :
    out₁ = out₂ := by
  rw [exactGramAppendixSearchProgram_eval] at h₁ h₂
  cases hi : (exactGramCharpolyInitializerProgram kernels A j 1).eval with
  | exact =>
      rw [hi] at h₁ h₂
      exact Option.some.inj (h₁.symm.trans h₂)
  | bracket l u =>
      simp only [hi] at h₁ h₂
      rw [exactGramAppendixSearchIndexed_eval] at h₁ h₂
      exact exactGramAppendixSearchIndexedValue_some_unique _ _
        (orderedEigenvalue A hA.isHermitian j) ε
        (fun i t b hb => exactGramAppendixEigenvalueQuery_correct kernels A hA.isHermitian j
          (g₁ i) t b hb)
        (fun i t b hb => exactGramAppendixEigenvalueQuery_correct kernels A hA.isHermitian j
          (g₂ i) t b hb) _ _ _ l u out₁ out₂ h₁ h₂

theorem exactGramAppendixUpperProgram_some_unique
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε)
    (g₁ g₂ : ExactGramAppendixSearchTape n ε hε) (u₁ u₂ : ℝ)
    (h₁ : (exactGramAppendixUpperProgram kernels A hA j ε hε g₁).eval = some u₁)
    (h₂ : (exactGramAppendixUpperProgram kernels A hA j ε hε g₂).eval = some u₂) :
    u₁ = u₂ := by
  simp only [exactGramAppendixUpperProgram, eval_bind, eval_pure] at h₁ h₂
  cases hs₁ : (exactGramAppendixSearchProgram kernels A hA j ε hε g₁).eval with
  | none => simp only [hs₁, Option.map_none] at h₁; cases h₁
  | some out₁ =>
      cases hs₂ : (exactGramAppendixSearchProgram kernels A hA j ε hε g₂).eval with
      | none => simp only [hs₂, Option.map_none] at h₂; cases h₂
      | some out₂ =>
          have ho := exactGramAppendixSearchProgram_some_unique kernels A hA j ε hε
            g₁ g₂ out₁ out₂ hs₁ hs₂
          subst out₂
          simp only [hs₁, Option.map_some] at h₁
          simp only [hs₂, Option.map_some] at h₂
          exact Option.some.inj (h₁.symm.trans h₂)

/-- A fixed successful upper endpoint exists. It is independent of every
Gaussian coordinate, and equals the actual output on a full-measure event.
This permits fresh jitter to be composed without a measurable-output premise. -/
theorem exactGramAppendixUpperProgram_fixed_output
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.PosSemidef) (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ uIdeal : ℝ,
      (orderedEigenvalue A hA.isHermitian j ≤ uIdeal ∧
        uIdeal ≤ (1+ε)*orderedEigenvalue A hA.isHermitian j) ∧
      (∀ g u, (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u →
        u = uIdeal) ∧
      (∀ᵐ g ∂exactGramAppendixSearchLaw n ε hε,
        (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some uIdeal) := by
  have hsuccess := exactGramAppendixUpperProgram_success_ae kernels A hA j ε hε
  obtain ⟨g₀, uIdeal, huIdeal, hlo, hhi⟩ := hsuccess.exists
  have hfixed : ∀ g u,
      (exactGramAppendixUpperProgram kernels A hA j ε hε g).eval = some u → u = uIdeal :=
    fun g u hu => exactGramAppendixUpperProgram_some_unique kernels A hA j ε hε
      g g₀ u uIdeal hu huIdeal
  refine ⟨uIdeal, ⟨hlo, hhi⟩, hfixed, ?_⟩
  filter_upwards [hsuccess] with g hg
  obtain ⟨u, hu, _⟩ := hg
  simpa only [hfixed g u hu] using hu

end
end HierarchicalAbsoluteSpectral
