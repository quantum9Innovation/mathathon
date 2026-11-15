import HierarchicalAbsoluteSpectral.BaseCost

/-! The manuscript's finite weighted-defect result for the actual true
Neumann pencil, with a counted field-and-scalar-square-root construction. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k : ℕ}

def BaseConstruction.castInputs {D E K0 L0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) (hD : D = E) (hK : K0 = L0) :
    BaseConstruction E L0 h hh := by cases hD; cases hK; exact out

theorem real_diagonal_const (n : ℕ) (c : ℝ) :
    Matrix.diagonal (fun _ : Fin n => c) = c • (1 : Core n) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

def coarseBaseProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h) :
    ArithmeticProgram (BaseConstruction (t • (1 : Core k)+Q0) (t • (1 : Core k)-Q0) h hh) := do
  let D ← certify (blockAddProgram (Matrix.diagonal (fun _ => t)) Q0)
  let K0 ← certify (blockSubProgram (Matrix.diagonal (fun _ => t)) Q0)
  have hDval : D.val = t • (1 : Core k)+Q0 := by
    rw [D.property, blockAddProgram_eval, real_diagonal_const]
  have hKval : K0.val = t • (1 : Core k)-Q0 := by
    rw [K0.property, blockSubProgram_eval, real_diagonal_const]
  have hD : D.val.PosDef := by
    rw [hDval]
    exact (Matrix.PosDef.one.smul ht).add_posSemidef hQ0
  have hQt : Q0ᵀ = Q0 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ0.isHermitian.eq
  have hK : K0.valᵀ = K0.val := by rw [hKval]; simp [hQt]
  let out ← baseConstructionProgram kernels D.val K0.val hD hK h hh
  ArithmeticProgram.pure (out.castInputs hDval hKval)

theorem coarseBaseProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h) :
    (coarseBaseProgram kernels Q0 hQ0 t ht h hh).work = baseConstructionCost kernels k h hh+2*k*k := by
  simp only [coarseBaseProgram, work_bind, certify_work, blockAddProgram_work,
    blockSubProgram_work, baseConstructionProgram_work, work_pure]
  ring

theorem coarseBaseProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h) :
    (coarseBaseProgram kernels Q0 hQ0 t ht h hh).admissible := by
  simp only [coarseBaseProgram, admissible_bind, certify_admissible,
    blockAddProgram_admissible, blockSubProgram_admissible, baseConstructionProgram_admissible,
    admissible_pure, and_self]

theorem exists_fast_coarse_base_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (Q0 : Core n) (hQ0 : Q0.PosSemidef) (t : ℝ) (ht : 0 < t)
        (h : ℝ) (hh : 0 < h), h ≤ 1/64 → 1 ≤ n →
        (coarseBaseProgram kernels Q0 hQ0 t ht h hh).admissible ∧
        ((coarseBaseProgram kernels Q0 hQ0 t ht h hh).work:ℝ) ≤
          C*(n:ℝ)^(9/4+ζ)*(1+4*Real.log (1/(4*h))) := by
  obtain ⟨kernels,C,hC,hwork⟩ := exists_fast_base_program ζ hζ
  refine ⟨kernels,C+2,by positivity,?_⟩
  intro n Q0 hQ0 t ht h hh hh' hn
  refine ⟨coarseBaseProgram_admissible kernels Q0 hQ0 t ht h hh,?_⟩
  have hD : (t • (1 : Core n)+Q0).PosDef := (Matrix.PosDef.one.smul ht).add_posSemidef hQ0
  have hQ0t : Q0ᵀ = Q0 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ0.isHermitian.eq
  have hK0 : (t • (1 : Core n)-Q0)ᵀ = t • (1 : Core n)-Q0 := by simp [hQ0t]
  have hb := (hwork n _ _ hD hK0 h hh hh' hn).2
  rw [baseConstructionProgram_work] at hb
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 ≤ (n:ℝ)^(9/4+ζ) := Real.rpow_nonneg (by positivity) _
  have hs : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)^(9/4+ζ) := by
    simpa only [Real.rpow_two, pow_two] using
      Real.rpow_le_rpow_of_exponent_le hnreal (show (2:ℝ) ≤ 9/4+ζ by linarith)
  have hlog : 0 ≤ Real.log (1/(4*h)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity : 0 < 4*h)).mpr
    linarith
  have he : 2*(n:ℝ)*(n:ℝ) ≤ 2*(n:ℝ)^(9/4+ζ)*(1+4*Real.log (1/(4*h))) := by
    nlinarith [mul_nonneg hnp hlog]
  rw [coarseBaseProgram_work]
  push_cast
  nlinarith

/-- The finite weighted-defect conclusion. The output F and its inverse
factor R come from the executed algorithm. The input assumptions are exactly
the coarse Gram and right-sketch inequalities and the mass accuracy. -/
theorem finite_weighted_defect (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (G Q Q0 : Core k) (hQ : Q.PosSemidef) (hQ0 : Q0.PosSemidef)
    (h ε t : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hε : 0 < ε) (hε' : ε ≤ h/100) (ht : 0 < t)
    (hGlo : (1/(1+h)) • (1 : Core k) ≤ G) (hGup : G ≤ (1/(1-h)) • (1 : Core k))
    (hQlo : (1-h) • Q ≤ Q0) (hQup : Q0 ≤ (1+h) • Q) :
    let out := (coarseBaseProgram kernels Q0 hQ0 t ht h hh).eval
    let F := out.metric
    let R := out.inverseFactor
    let K := trueNeumannPencil G Q t ε hε
    let D := t • (1 : Core k)+Q0
    IsUnit R.det ∧ inverseMetric R = F ∧
      F.PosDef ∧ (8*h) • D ≤ F ∧ F ≤ (2:ℝ) • D ∧
      (6*h) • D ≤ F-K ∧ (6*h) • D ≤ F+K ∧
      (F-K).PosDef ∧ (F+K).PosDef ∧
      (0 : Core k) ≤ F-K*F⁻¹*K ∧ F-K*F⁻¹*K ≤ (36*h) • D := by
  let out := (coarseBaseProgram kernels Q0 hQ0 t ht h hh).eval
  have he := constructed_base_pencil_error G Q Q0 h ε t hh hh' hε hε' ht.le hQ
    hGlo hGup hQlo hQup
  have hb := base_pencil_bands Q0 t ht.le hQ0
  have hg := coarse_gram_inverse_bands G h hh hh' hGlo hGup
  have hm := constructedNeumannMass_posDef G hg.1.isHermitian ε hε
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hQ0t : Q0ᵀ = Q0 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ0.isHermitian.eq
  have hmt : (constructedNeumannMass G ε hε)ᵀ = constructedNeumannMass G ε hε := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hm.isHermitian.eq
  have hK : (trueNeumannPencil G Q t ε hε)ᵀ = trueNeumannPencil G Q t ε hε := by
    simp [trueNeumannPencil, hQt, hmt]
  have hK0 : (t • (1 : Core k)-Q0)ᵀ = t • (1 : Core k)-Q0 := by simp [hQ0t]
  exact ⟨out.inverseFactor_isUnit, out.inverseFactor_metric,
    out.invariant _ hK0 hK hh' hb.1 hb.2 he.1 he.2⟩

end
end HierarchicalAbsoluteSpectral
