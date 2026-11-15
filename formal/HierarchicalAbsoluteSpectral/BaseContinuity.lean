import HierarchicalAbsoluteSpectral.CholeskyContinuity
import HierarchicalAbsoluteSpectral.BaseTheorem

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {X : Type*} [TopologicalSpace X] {k : ℕ}

theorem upperNewtonMatrix_continuous (M : X → Core k) (hM : Continuous M)
    (hpos : ∀ x q, (upperNewtonMatrix (M x) q).PosDef) (q : ℕ) :
    Continuous (fun x => upperNewtonMatrix (M x) q) := by
  induction q with
  | zero => simp only [upperNewtonMatrix]; exact continuous_const
  | succ q ih =>
    have hi := continuous_matrix_inverse (fun x => upperNewtonMatrix (M x) q) ih
      (fun x => isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hpos x q).isUnit))
    simpa only [upperNewtonMatrix,Pi.add_apply] using continuous_const.smul (ih.add (hM.matrix_mul hi))

theorem baseNewtonMetric_continuous (S : X → Core k) (hS : Continuous S)
    (hHerm : ∀ x, (S x).IsHermitian) (h : ℝ) (hh : 0 < h) (q : ℕ) :
    Continuous (fun x => baseNewtonMetric (S x) h q) := by
  have hc : Continuous (fun x => S x*S x+(8*h)^2 • (1 : Core k)) :=
    (hS.matrix_mul hS).add continuous_const
  have hp : ∀ x n, (upperNewtonMatrix (S x*S x+(8*h)^2 • (1 : Core k)) n).PosDef :=
    fun x n => baseNewtonIterate_posDef (S x) (hHerm x) h hh n
  exact (upperNewtonMatrix_continuous _ hc hp q).add continuous_const

theorem baseConstructionProgram_dFactor (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.dFactor =
      (choleskyProgram kernels k D hD).eval := by
  unfold baseConstructionProgram
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_pure]

theorem baseConstructionProgram_metric (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.metric =
      baseCoreMetric (choleskyProgram kernels k D hD).eval.upper K0 h hh := by
  calc
    _ = baseCoreMetric (baseConstructionProgram kernels D K0 hD hK h hh).eval.dFactor.upper K0 h hh :=
      (baseConstructionProgram kernels D K0 hD hK h hh).eval.metric_eq
    _ = _ := by rw [baseConstructionProgram_dFactor]

theorem baseCoreMetric_posDef (J K0 : Core k) (hJ : IsUnit J) (hK : K0ᵀ = K0)
    (h : ℝ) (hh : 0 < h) : (baseCoreMetric J K0 h hh).PosDef := by
  have hf := baseNewtonMetric_posDef (baseNormalized J K0)
    (normalized_isHermitian J⁻¹ K0 hK) h hh (baseNewtonSteps h hh)
  have hi : Function.Injective J.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hJ
  simpa only [baseCoreMetric,Matrix.conjTranspose_eq_transpose_of_trivial] using
    hf.conjTranspose_mul_mul_same hi

theorem baseConstructionProgram_metric_posDef
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.metric.PosDef := by
  rw [baseConstructionProgram_metric]
  exact baseCoreMetric_posDef _ _ (choleskyProgram kernels k D hD).eval.isUnit hK h hh

theorem choleskyProgram_inverse_congr (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n : ℕ} {D E : Core n} (hD : D.PosDef) (hE : E.PosDef) (h : D = E) :
    (choleskyProgram kernels n D hD).eval.inverse = (choleskyProgram kernels n E hE).eval.inverse := by
  subst E
  rfl

theorem baseConstructionProgram_inverseFactor_of_metric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK : K0ᵀ = K0) (h : ℝ) (hh : 0 < h)
    (F : Core k) (hF : F.PosDef)
    (hMetric : F = (baseConstructionProgram kernels D K0 hD hK h hh).eval.metric) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.inverseFactor =
      (choleskyProgram kernels k F hF).eval.inverse := by
  unfold baseConstructionProgram at hMetric ⊢
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_pure] at hMetric
  rw [eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_bind,eval_pure]
  apply choleskyProgram_inverse_congr
  exact hMetric.symm

theorem baseConstructionProgram_inverseFactor
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : Core k) (hD : D.PosDef) (hK : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.inverseFactor =
      (choleskyProgram kernels k
        (baseConstructionProgram kernels D K0 hD hK h hh).eval.metric
        (baseConstructionProgram_metric_posDef kernels D K0 hD hK h hh)).eval.inverse := by
  exact baseConstructionProgram_inverseFactor_of_metric kernels D K0 hD hK h hh _ _ rfl

theorem baseConstructionProgram_metric_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : X → Core k) (hD : ∀ x, (D x).PosDef) (hK : ∀ x, (K0 x)ᵀ = K0 x)
    (hDc : Continuous D) (hKc : Continuous K0) (h : ℝ) (hh : 0 < h) :
    Continuous (fun x => (baseConstructionProgram kernels (D x) (K0 x) (hD x) (hK x) h hh).eval.metric) := by
  let p := fun x => (choleskyProgram kernels k (D x) (hD x)).eval
  have hpc := choleskyProgram_continuous kernels k D hD hDc
  have hNorm : Continuous (fun x => baseNormalized (p x).upper (K0 x)) := by
    have hi : Continuous (fun x => (p x).upper⁻¹) := by
      have he : (fun x => (p x).upper⁻¹) = (fun x => (p x).inverse) :=
        funext (fun x => (p x).inverse_eq.symm)
      rw [he]
      exact hpc.2
    exact (hi.matrix_transpose.matrix_mul hKc).matrix_mul hi
  have hF := baseNewtonMetric_continuous _ hNorm
    (fun x => normalized_isHermitian (p x).upper⁻¹ (K0 x) (hK x)) h hh (baseNewtonSteps h hh)
  have he : (fun x => (baseConstructionProgram kernels (D x) (K0 x) (hD x) (hK x) h hh).eval.metric) =
      (fun x => baseCoreMetric (p x).upper (K0 x) h hh) :=
    funext (fun x => baseConstructionProgram_metric kernels (D x) (K0 x) (hD x) (hK x) h hh)
  rw [he]
  exact (hpc.1.matrix_transpose.matrix_mul hF).matrix_mul hpc.1

theorem baseConstructionProgram_inverseFactor_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (D K0 : X → Core k) (hD : ∀ x, (D x).PosDef) (hK : ∀ x, (K0 x)ᵀ = K0 x)
    (hDc : Continuous D) (hKc : Continuous K0) (h : ℝ) (hh : 0 < h) :
    Continuous (fun x => (baseConstructionProgram kernels (D x) (K0 x) (hD x) (hK x) h hh).eval.inverseFactor) := by
  have hF := baseConstructionProgram_metric_continuous kernels D K0 hD hK hDc hKc h hh
  have hfpos := fun x => baseConstructionProgram_metric_posDef kernels (D x) (K0 x) (hD x) (hK x) h hh
  have hFc := (choleskyProgram_continuous kernels k _ hfpos hF).2
  have he : (fun x => (baseConstructionProgram kernels (D x) (K0 x) (hD x) (hK x) h hh).eval.inverseFactor) =
      (fun x => (choleskyProgram kernels k
        (baseConstructionProgram kernels (D x) (K0 x) (hD x) (hK x) h hh).eval.metric (hfpos x)).eval.inverse) :=
    funext (fun x => baseConstructionProgram_inverseFactor kernels (D x) (K0 x) (hD x) (hK x) h hh)
  rw [he]
  exact hFc

@[simp] theorem BaseConstruction.castInputs_inverseFactor
    {D E K0 L0 : Core k} {h : ℝ} {hh : 0 < h}
    (out : BaseConstruction D K0 h hh) (hD : D = E) (hK : K0 = L0) :
    (out.castInputs hD hK).inverseFactor = out.inverseFactor := by
  cases hD
  cases hK
  rfl

theorem baseConstructionProgram_inverseFactor_congr
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D E K0 L0 : Core k} (hD : D.PosDef) (hE : E.PosDef)
    (hK : K0ᵀ = K0) (hL : L0ᵀ = L0) (h : ℝ) (hh : 0 < h)
    (hDE : D = E) (hKL : K0 = L0) :
    (baseConstructionProgram kernels D K0 hD hK h hh).eval.inverseFactor =
      (baseConstructionProgram kernels E L0 hE hL h hh).eval.inverseFactor := by
  subst E
  subst L0
  rfl

theorem coarseBaseProgram_inverseFactor_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (t : ℝ) (ht : 0 < t) (h : ℝ) (hh : 0 < h)
    (hD : (t • (1 : Core k)+Q0).PosDef) (hK : (t • (1 : Core k)-Q0)ᵀ = t • (1 : Core k)-Q0) :
    (coarseBaseProgram kernels Q0 hQ0 t ht h hh).eval.inverseFactor =
      (baseConstructionProgram kernels (t • (1 : Core k)+Q0)
        (t • (1 : Core k)-Q0) hD hK h hh).eval.inverseFactor := by
  unfold coarseBaseProgram
  rw [eval_bind,eval_bind,eval_bind,eval_pure]
  rw [BaseConstruction.castInputs_inverseFactor]
  apply baseConstructionProgram_inverseFactor_congr
  · simp only [certify_eval,blockAddProgram_eval,real_diagonal_const]
  · simp only [certify_eval,blockSubProgram_eval,real_diagonal_const]

/-- The actual computed inverse factor is continuous on the complete
positive threshold domain. The matrices, scalar schedule and kernel family
are fixed, while every Cholesky/Newton output remains the executed one. -/
theorem coarseBaseProgram_inverseFactor_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (h : ℝ) (hh : 0 < h) :
    Continuous (fun t : {t : ℝ // 0 < t} =>
      (coarseBaseProgram kernels Q0 hQ0 t.val t.property h hh).eval.inverseFactor) := by
  let D := fun t : {t : ℝ // 0 < t} => t.val • (1 : Core k)+Q0
  let K := fun t : {t : ℝ // 0 < t} => t.val • (1 : Core k)-Q0
  have hD : ∀ t, (D t).PosDef := fun t =>
    (Matrix.PosDef.one.smul t.property).add_posSemidef hQ0
  have hQt : Q0ᵀ = Q0 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ0.isHermitian.eq
  have hK : ∀ t, (K t)ᵀ = K t := by intro t; simp [K,hQt]
  have hDc : Continuous D := (continuous_subtype_val.smul continuous_const).add continuous_const
  have hKc : Continuous K := (continuous_subtype_val.smul continuous_const).sub continuous_const
  have hc := baseConstructionProgram_inverseFactor_continuous kernels D K hD hK hDc hKc h hh
  have he : (fun t : {t : ℝ // 0 < t} =>
      (coarseBaseProgram kernels Q0 hQ0 t.val t.property h hh).eval.inverseFactor) =
      (fun t => (baseConstructionProgram kernels (D t) (K t) (hD t) (hK t) h hh).eval.inverseFactor) :=
    funext (fun t => coarseBaseProgram_inverseFactor_eq kernels Q0 hQ0 t.val t.property h hh (hD t) (hK t))
  rw [he]
  exact hc

end
end HierarchicalAbsoluteSpectral
