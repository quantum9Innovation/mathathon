import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Finite product Gaussian inputs, their one-dimensional projection law, and
an elementary interval small-ball estimate used by the column-distance
argument. All probabilities below are Mathlib measures.

The projection-law proof follows the Mathlib standard-Gaussian construction;
the same public API route is used in claytomode/johnson-lindenstrauss-lean,
JL/Rotation.lean (Apache-2.0, revision
599963af7a8f79e07ce0be57c53a62f70b38b365).
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

def gaussianVector (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance gaussianVector_isProbability (n : ℕ) : IsProbabilityMeasure (gaussianVector n) := by
  unfold gaussianVector
  infer_instance

/-- Column-major finite array of independent standard real Gaussians. -/
def gaussianColumns (n r : ℕ) : Measure (Fin r → Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianVector n)

instance gaussianColumns_isProbability (n r : ℕ) : IsProbabilityMeasure (gaussianColumns n r) := by
  unfold gaussianColumns
  infer_instance

theorem gaussianPDFReal_unit_le_one (μ x : ℝ) : gaussianPDFReal μ 1 x ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (2*Real.pi) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity),
      Real.sqrt_nonneg (2*Real.pi), Real.pi_gt_three]
  have hi : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr hs
  have he : Real.exp (-(x-μ)^2/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x-μ)])
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  exact (mul_le_mul hi he (Real.exp_nonneg _) zero_le_one).trans (by norm_num)

theorem gaussianReal_unit_small_ball (μ c t : ℝ) (_ht : 0 ≤ t) :
    gaussianReal μ 1 {x : ℝ | |x-c| ≤ t} ≤ ENNReal.ofReal (2*t) := by
  have hset : {x : ℝ | |x-c| ≤ t} = Icc (c-t) (c+t) := by
    ext x
    simp only [mem_setOf_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hset, gaussianReal_apply μ (by norm_num)]
  calc
    _ ≤ ∫⁻ _x in Icc (c-t) (c+t), (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro x
      rw [gaussianPDF, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_unit_le_one μ x)
    _ = volume (Icc (c-t) (c+t)) := by simp
    _ = ENNReal.ofReal (2*t) := by rw [Real.volume_Icc]; congr 1; ring

/-- A unit linear projection of the finite standard Gaussian product is
exactly N(0,1), including the distributional equality needed by conditioning. -/
theorem gaussianVector_unit_projection (n : ℕ) (u : Fin n → ℝ)
    (hu : ∑ i, u i^2 = 1) :
    (gaussianVector n).map (fun x => ∑ i, x i*u i) = gaussianReal 0 1 := by
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ y
  have hm : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  have hL : Measurable L := L.continuous.measurable
  have heq : (fun x : Fin n → ℝ => ∑ i, x i*u i) = L ∘ WithLp.toLp 2 := by
    funext x
    simp only [L, y]
    apply Finset.sum_congr rfl
    intro i hi
    simp [RCLike.inner_apply, mul_comm]
  have hstd : (gaussianVector n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    map_pi_eq_stdGaussian
  have hgl : HasGaussianLaw L (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id.map L
  have hnorm : ‖L‖^2 = 1 := by
    rw [show L = innerSL ℝ y from rfl, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
    exact hu
  rw [heq, ← Measure.map_map hL hm, hstd, hgl.map_eq_gaussianReal,
    integral_strongDual_stdGaussian L, variance_dual_stdGaussian L, hnorm, Real.toNNReal_one]

theorem gaussianVector_projection_small_ball (n : ℕ) (u : Fin n → ℝ)
    (hu : ∑ i, u i^2 = 1) (c t : ℝ) (ht : 0 ≤ t) :
    gaussianVector n {x | |(∑ i, x i*u i)-c| ≤ t} ≤ ENNReal.ofReal (2*t) := by
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i*u i) := by fun_prop
  have hset : MeasurableSet {x : ℝ | |x-c| ≤ t} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have h := gaussianReal_unit_small_ball 0 c t ht
  rw [← gaussianVector_unit_projection n u hu, Measure.map_apply hm hset] at h
  exact h

theorem gaussianReal_unit_second_moment : ∫ x : ℝ, x^2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [id_eq, integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h

end
end HierarchicalAbsoluteSpectral
