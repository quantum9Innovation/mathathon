import HierarchicalAbsoluteSpectral.StrongFilterProgram
import HierarchicalAbsoluteSpectral.ThresholdKrylovDegree

/-! Actual physical output basis and the exact first sufficient strong degree. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open ArithmeticProgram hiding pure
variable {n k r : ℕ}

def strongGaussianDegreeProgram (k : ℕ) (U β α : ℝ)
    (hk : 1≤k) (hU : 1≤U) (hβ : 0<β) (hβ1 : β≤1) (hα : 0<α) (hα1 : α≤1) :
    ArithmeticProgram ℕ := do
  let R ← (gaussianCaptureRadiusProgram k U β).certify
  let D ← (show ArithmeticProgram ℝ from do
    let a ← mul 2 R.val
    div a α).certify
  have he : D.val=2*gaussianCaptureRadius k U β/α := by
    simpa only [eval_bind, eval_mul, eval_div, R.property, gaussianCaptureRadiusProgram_eval] using D.property
  strongDegreeProgram α D.val hα hα1
    (by rw [he]; exact strongGaussianDenominator_ge_one k U β α hk hU hβ hβ1 hα hα1)

theorem strongGaussianDegreeProgram_specification (k : ℕ) (U β α : ℝ)
    (hk : 1≤k) (hU : 1≤U) (hβ : 0<β) (hβ1 : β≤1) (hα : 0<α) (hα1 : α≤1) :
    (strongGaussianDegreeProgram k U β α hk hU hβ hβ1 hα hα1).eval=
      strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1 ∧
    (strongGaussianDegreeProgram k U β α hk hU hβ hβ1 hα hα1).work=
      4*strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1+14 ∧
    (strongGaussianDegreeProgram k U β α hk hU hβ hβ1 hα hα1).admissible := by
  simp only [strongGaussianDegreeProgram, eval_bind, work_bind, admissible_bind,
    certify_eval, certify_work, certify_admissible, gaussianCaptureRadiusProgram_eval,
    gaussianCaptureRadiusProgram_work, gaussianCaptureRadiusProgram_admissible _ _ _ hβ.ne',
    eval_mul, eval_div, work_mul, work_div, admissible_mul, admissible_div,
    admissible_pure, work_pure, add_zero, hα.ne', true_and, and_true]
  have hs := strongDegreeProgram_specification α (2*gaussianCaptureRadius k U β/α) hα hα1
    (strongGaussianDenominator_ge_one k U β α hk hU hβ hβ1 hα hα1)
  refine ⟨hs.1,?_,hα.ne',hs.2.2⟩
  have hw := hs.2.1
  change _=4*strongFilterDegree α (2*gaussianCaptureRadius k U β/α) hα hα1 _+14
  omega

/-- A good physical certificate holds for the basis computed by the actual
range program, including lost or dependent filtered columns. -/
theorem physical_strong_certificate_of_range
    (Z : Matrix (Fin n) (Fin k) ℝ) (R K : Core k)
    (Y : (Fin r → Fin k → ℝ) → Matrix (Fin n) (Fin r) ℝ) (α : ℝ)
    (G : Fin r → Fin k → ℝ) (hG : G∈physicalStrongSuccess Z R K Y α)
    (out : OrthogonalRange (Y G)) :
    out.dimension≤r ∧ out.basisᵀ*out.basis=1 ∧
      ∀ x : Fin n → ℝ, out.basisᵀ*ᵥx=0 →
        quadratic (K*(inverseMetric R)⁻¹*K) (Zᵀ*ᵥx)-2*quadratic K (Zᵀ*ᵥx)≤
          ((1+3*α)^2-1)*quadratic (inverseMetric R) (Zᵀ*ᵥx) := by
  obtain ⟨w,hw,V,hV,B,C,hY,hC,hcert⟩ := hG
  refine ⟨out.dimension_le_cols,out.orthogonal,?_⟩
  intro x hx
  have hYx : (Y G)ᵀ*ᵥx=0 := by
    rw [out.spans, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hVx : Vᵀ*ᵥx=0 := by
    rw [hC, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hYx, Matrix.mulVec_zero]
  exact hcert x hVx

def automaticStrongPhysicalRangeProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {L : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A r) (PL : MatrixAction L r)
    (U β α : ℝ) (hk : 1≤k) (hU : 1≤U) (hβ : 0<β) (hβ1 : β≤1) (hα : 0<α) (hα1 : α≤1)
    (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    ArithmeticProgram (Σ v : ℕ, OrthogonalRange (L*(Polynomial.aeval A (strongFilterPolynomial α v)*Ξ))) := do
  let v ← strongGaussianDegreeProgram k U β α hk hU hβ hβ1 hα hα1
  let out ← strongPhysicalRangeProgram kernels P PL α v hα Ξ
  ArithmeticProgram.pure ⟨v,out⟩

theorem automaticStrongPhysicalRangeProgram_degree
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {L : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A r) (PL : MatrixAction L r)
    (U β α : ℝ) (hk : 1≤k) (hU : 1≤U) (hβ : 0<β) (hβ1 : β≤1) (hα : 0<α) (hα1 : α≤1)
    (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (automaticStrongPhysicalRangeProgram kernels P PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval.1=
      strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1 := by
  simp only [automaticStrongPhysicalRangeProgram, eval_bind, eval_pure]
  exact (strongGaussianDegreeProgram_specification _ _ _ _ _ _ _ _ _ _).1

theorem automaticStrongPhysicalRangeProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {L : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A r) (PL : MatrixAction L r)
    (U β α : ℝ) (hk : 1≤k) (hU : 1≤U) (hβ : 0<β) (hβ1 : β≤1) (hα : 0<α) (hα1 : α≤1)
    (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (automaticStrongPhysicalRangeProgram kernels P PL U β α hk hU hβ hβ1 hα hα1 Ξ).admissible := by
  simp only [automaticStrongPhysicalRangeProgram, admissible_bind, admissible_pure,
    strongPhysicalRangeProgram_admissible, and_true]
  exact (strongGaussianDegreeProgram_specification _ _ _ _ _ _ _ _ _ _).2.2

end
end HierarchicalAbsoluteSpectral
