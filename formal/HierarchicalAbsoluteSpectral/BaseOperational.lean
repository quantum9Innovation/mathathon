import HierarchicalAbsoluteSpectral.NewtonProgram
import HierarchicalAbsoluteSpectral.BasePencil

/-! The complete executed finite base construction: factor D, normalize,
run upper Newton iteration, conjugate, and factor the resulting metric. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k : ℕ}

structure BaseConstruction (D K0 : Core k) (h : ℝ) (hh : 0 < h) where
  dFactor : FiniteGramPair D
  metric : Core k
  metric_eq : metric = baseCoreMetric dFactor.upper K0 h hh
  metricFactor : FiniteGramPair metric

namespace BaseConstruction

def inverseFactor {D K0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) : Core k := out.metricFactor.inverse

theorem inverseFactor_isUnit {D K0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) : IsUnit out.inverseFactor.det := by
  rw [inverseFactor, out.metricFactor.inverse_eq]
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.isUnit_nonsing_inv_iff.mpr out.metricFactor.isUnit)

theorem inverseFactor_metric {D K0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) : inverseMetric out.inverseFactor = out.metric := by
  let p := out.metricFactor
  letI := p.isUnit.invertible
  change (p.inverse⁻¹)ᵀ*p.inverse⁻¹ = _
  rw [p.inverse_eq, Matrix.inv_inv_of_invertible]
  exact p.gram

theorem invariant {D K0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) (K : Core k)
    (hK0 : K0ᵀ = K0) (hK : Kᵀ = K) (hh' : h ≤ 1/64)
    (hK0lo : -D ≤ K0) (hK0up : K0 ≤ D)
    (helo : -((2*h) • D) ≤ K-K0) (heup : K-K0 ≤ (2*h) • D) :
    out.metric.PosDef ∧ (8*h) • D ≤ out.metric ∧ out.metric ≤ (2:ℝ) • D ∧
      (6*h) • D ≤ out.metric-K ∧ (6*h) • D ≤ out.metric+K ∧
      (out.metric-K).PosDef ∧ (out.metric+K).PosDef ∧
      (0 : Core k) ≤ out.metric-K*out.metric⁻¹*K ∧
      out.metric-K*out.metric⁻¹*K ≤ (36*h) • D := by
  rw [out.metric_eq]
  exact base_core_invariant out.dFactor.upper D K0 K h
    ((Matrix.isUnit_iff_isUnit_det _).mp out.dFactor.isUnit) out.dFactor.gram
    hK0 hK hh hh' hK0lo hK0up helo heup

end BaseConstruction

def baseConstructionProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    ArithmeticProgram (BaseConstruction D K0 h hh) := do
  let p ← choleskyProgram kernels k D hD
  let L ← certify ((kernels k k k).program p.inverseᵀ K0)
  let S ← certify ((kernels k k k).program L.val p.inverse)
  have hSval : S.val = baseNormalized p.upper K0 := by
    simp only [S.property, ArithmeticKernel.program_eval, L.property,
      p.inverse_eq, baseNormalized]
  have hS : S.val.IsHermitian := by
    rw [hSval]
    exact normalized_isHermitian p.upper⁻¹ K0 hK0
  let Fb ← baseNewtonProgram kernels S.val hS h hh (baseNewtonSteps h hh)
  let F1 ← certify ((kernels k k k).program p.upperᵀ Fb.val)
  let F ← certify ((kernels k k k).program F1.val p.upper)
  have hFval : F.val = baseCoreMetric p.upper K0 h hh := by
    simp only [F.property, ArithmeticKernel.program_eval, F1.property, Fb.property,
      hSval, baseCoreMetric]
  have hFpos : F.val.PosDef := by
    have hFb : Fb.val.PosDef := by
      rw [Fb.property]
      exact baseNewtonMetric_posDef S.val hS h hh _
    have hf := hFb.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr p.isUnit)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, F.property,
      ArithmeticKernel.program_eval, F1.property] using hf
  let q ← choleskyProgram kernels k F.val hFpos
  ArithmeticProgram.pure ⟨p, F.val, hFval, q⟩

def baseConstructionCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (k : ℕ) (h : ℝ) (hh : 0 < h) : ℕ :=
  2*choleskyCost kernels k+5*(kernels k k k).cost+2+2*k*k+
    baseNewtonSteps h hh*(choleskyCost kernels k+2*(kernels k k k).cost+2*k*k)

theorem baseConstructionProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK0 h hh).work = baseConstructionCost kernels k h hh := by
  simp only [baseConstructionProgram, work_bind, choleskyProgram_work, certify_work,
    ArithmeticKernel.program_work, baseNewtonProgram_work, work_pure, baseConstructionCost]
  ring

theorem baseConstructionProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK0 h hh).admissible := by
  simp only [baseConstructionProgram, admissible_bind, choleskyProgram_admissible,
    certify_admissible, ArithmeticKernel.program_admissible, baseNewtonProgram_admissible,
    admissible_pure, and_self]

theorem baseConstructionProgram_invariant (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 K : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0) (hK : Kᵀ = K)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hK0lo : -D ≤ K0) (hK0up : K0 ≤ D)
    (helo : -((2*h) • D) ≤ K-K0) (heup : K-K0 ≤ (2*h) • D) :
    let out := (baseConstructionProgram kernels D K0 hD hK0 h hh).eval
    let F := out.metric
    F.PosDef ∧ (8*h) • D ≤ F ∧ F ≤ (2:ℝ) • D ∧
      (6*h) • D ≤ F-K ∧ (6*h) • D ≤ F+K ∧
      (F-K).PosDef ∧ (F+K).PosDef ∧
      (0 : Core k) ≤ F-K*F⁻¹*K ∧ F-K*F⁻¹*K ≤ (36*h) • D := by
  exact (baseConstructionProgram kernels D K0 hD hK0 h hh).eval.invariant K
    hK0 hK hh' hK0lo hK0up helo heup

end
end HierarchicalAbsoluteSpectral
