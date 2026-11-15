import HierarchicalAbsoluteSpectral.MainStatementsFixed
import HierarchicalAbsoluteSpectral.StrongOutput

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n m p k r : ℕ}
attribute [local irreducible] automaticStrongPhysicalRangeProgram

def strongProjectionOutputProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    ArithmeticProgram (FixedRankOutput n p r) := do
  let out ← automaticStrongPhysicalRangeProgram kernels PT PL U β α hk hU hβ hβ1 hα hα1 Ξ
  projectionOutputProgram kernels A B out.2.basis out.2.dimension_le_cols

theorem strongProjectionOutputProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (strongProjectionOutputProgram kernels A B PT PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval =
      (projectionOutputProgram kernels A B
        (automaticStrongPhysicalRangeProgram kernels PT PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.basis
        (automaticStrongPhysicalRangeProgram kernels PT PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval.2.dimension_le_cols).eval :=
  ArithmeticProgram.eval_bind _ _

theorem strongProjectionOutputProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (strongProjectionOutputProgram kernels A B PT PL U β α hk hU hβ hβ1 hα hα1 Ξ).admissible := by
  simp only [strongProjectionOutputProgram,admissible_bind,automaticStrongPhysicalRangeProgram_admissible,
    projectionOutputProgram_admissible,and_self]

theorem strongProjectionOutputProgram_projected_product
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    let result := (strongProjectionOutputProgram kernels A B PT PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval
    result.product=result.left*(result.leftᵀ*(A*B)) := by
  dsimp only
  rw [strongProjectionOutputProgram_eval,projectionOutputProgram_eval]
  simp only [Matrix.mul_assoc]

theorem strongProjectionOutputProgram_dual_certificate
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    {T : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ}
    (PT : MatrixAction T r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (Z : Matrix (Fin n) (Fin k) ℝ) (R K : Core k) (G : Fin r → Fin k → ℝ)
    (hG : G ∈ physicalStrongSuccess Z R K
      (fun G' => Lmap*(Polynomial.aeval T (strongFilterPolynomial α
        (automaticStrongPhysicalRangeProgram kernels PT PL U β α hk hU hβ hβ1 hα hα1
          (columnsMatrix G')).eval.1)*columnsMatrix G')) α) :
    let result := (strongProjectionOutputProgram kernels A B PT PL U β α hk hU hβ hβ1 hα hα1
      (columnsMatrix G)).eval
    result.leftᵀ*result.left=1 ∧ ∀ x : Fin n → ℝ, result.leftᵀ*ᵥx=0 →
      quadratic (K*(inverseMetric R)⁻¹*K) (Zᵀ*ᵥx)-2*quadratic K (Zᵀ*ᵥx) ≤
        ((1+3*α)^2-1)*quadratic (inverseMetric R) (Zᵀ*ᵥx) := by
  dsimp only
  let out := (automaticStrongPhysicalRangeProgram kernels PT PL U β α hk hU hβ hβ1 hα hα1
    (columnsMatrix G)).eval
  have hc := physical_strong_certificate_of_range Z R K _ α G hG out.2
  rw [strongProjectionOutputProgram_eval,projectionOutputProgram_eval]
  exact ⟨hc.2.1,hc.2.2⟩

end
end HierarchicalAbsoluteSpectral
