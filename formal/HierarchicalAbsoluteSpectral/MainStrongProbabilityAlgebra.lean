import HierarchicalAbsoluteSpectral.MainOperatorSpectral
import HierarchicalAbsoluteSpectral.MainStatementsTransfer

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Polynomial WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

abbrev mainStrongBase (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) : MainBaseData I S C t.val :=
  (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval

theorem mainBase_mul_source (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    base.inverseFactor*mainSourceFactor I S C t base = mainRefinedFactor I S C t base := by
  rw [mainSourceFactor,BaseConstruction.inverseFactor,← Matrix.mul_assoc,base.metricFactor.left_inverse,Matrix.one_mul]

theorem mainSourceFactor_isUnit (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t)
    (hR : IsUnit (mainRefinedFactor I S C t base).det) :
    IsUnit (mainSourceFactor I S C t base).det := by
  rw [mainSourceFactor_eq,Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det base.inverseFactor base.inverseFactor_isUnit).mul hR

theorem mainFilteredOperator_eq (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    filteredOperator (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)
      (mainSourceFactor I S C t base) = mainThresholdOperator I S C t base := by
  have hh : filteredOperator (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)
      (mainSourceFactor I S C t base) =
      1-normalizedPencil (base.inverseFactor*mainSourceFactor I S C t base) (mainTruePencil I S C t) := by
    simp only [filteredOperator,normalizedPencil,Matrix.transpose_mul,Matrix.mul_assoc]
  rw [hh,mainBase_mul_source]
  rfl

theorem mainPhysicalPolynomial_eq_lift (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t)
    (hR : IsUnit (mainRefinedFactor I S C t base).det) (α : ℝ) (v : ℕ)
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
      (aeval (mainCarriedMatrix I S C t base) (strongFilterPolynomial α v)*columnsMatrix G) =
    supportLeftFactor I.A S.initialA C.pair*((mainRefinedFactor I S C t base)⁻¹)ᵀ*
      strongGaussianOutput (mainThresholdOperator I S C t base) (mainSourceFactor I S C t base) α v G := by
  have hh := exact_physical_lift (supportLeftFactor I.A S.initialA C.pair) base.inverseFactor
    (mainSourceFactor I S C t base) (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)
    (mainSourceFactor_isUnit I S C t base hR) (strongFilterPolynomial α v) (columnsMatrix G)
  rw [mainBase_mul_source,mainFilteredOperator_eq,← mainCarriedMatrix_eq,mainBase_inverse_eq_upper] at hh
  simpa only [strongGaussianOutput,Matrix.mul_assoc] using hh.symm

theorem strongEigenvalues_bounds_of_order {k : ℕ} (T : Core k)
    (hT : T.toEuclideanLin.IsSymmetric) (hPSD : T.PosSemidef)
    (hUpper : T ≤ (2 : ℝ) • (1 : Core k)) :
    (∀ i, 0 ≤ strongEigenvalues T hT i) ∧ (∀ i, strongEigenvalues T hT i ≤ 2) := by
  refine ⟨fun i => orderedEigenvalue_nonneg T hPSD i,?_⟩
  intro i
  let v := strongSpectralBasis T hT i
  have hv : ‖v‖ = 1 := (strongSpectralBasis T hT).orthonormal.norm_eq_one i
  have he : quadratic T (ofLp v) = strongEigenvalues T hT i := by
    rw [quadratic_eq_inner]
    exact eigenvalue_rayleigh T.toEuclideanLin hT finrank_euclideanSpace_fin i
  have hh := quadratic_mono hUpper (ofLp v)
  rw [he,quadratic_smul,quadratic_one_norm,hv] at hh
  norm_num at hh
  exact hh

end
end HierarchicalAbsoluteSpectral
