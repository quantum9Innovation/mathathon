import HierarchicalAbsoluteSpectral.MainStrongProbabilityProgram

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem mainStrongPhysicalPolynomial_good_event (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t})
    (htarget : orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨r,hr⟩ ≤ 1+I.alpha) :
    ∃ E : Set (Fin r → Fin C.pair.dimension → ℝ), MeasurableSet E ∧
      (gaussianColumns C.pair.dimension r).real E ≥ 1-I.singleFailure ∧
        ∀ G ∈ E, G ∈ physicalStrongSuccess (supportLeftFactor I.A S.initialA C.pair)
          (mainRefinedFactor I S C t.val (mainStrongBase kernels I S C t)) (mainTruePencil I S C t.val)
          (mainStrongPhysicalPolynomial kernels I S C hk t) I.alpha := by
  let base := mainStrongBase kernels I S C t
  let R := mainRefinedFactor I S C t.val base
  let K := mainTruePencil I S C t.val
  let T := mainThresholdOperator I S C t.val base
  let source := mainSourceFactor I S C t.val base
  let Sinv := R⁻¹*base.inverseFactor
  let a := (1+hierarchyUpper L/(8*I.accuracy 0))⁻¹
  let b := 1+hierarchyUpper 0/(8*I.accuracy L)
  let hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (mainThresholdOperator_isHermitian I S C t.val base)
  have hf := hg.actual_hierarchy kernels I S C t.val t.property
  have hb := hg.actual_threshold_bounds kernels I S C t.val t.property
  obtain ⟨hleft,ha,hInv,hSnorm,hRatio,hU⟩ := hg.actual_source_condition kernels I S C t.val t.property
  have hcond : ‖source‖/a ≤ mainConditionBound I :=
    (div_le_div_of_nonneg_right hSnorm ha.le).trans hRatio
  have hd := strongEigenvalues_bounds_of_order T hs hb.1 hb.2
  have htail : ∀ i : Fin C.pair.dimension, r ≤ i.val → strongEigenvalues T hs i ≤ 1+I.alpha := by
    intro i hi
    exact (hs.eigenvalues_antitone (by simp) (show (⟨r,hr⟩ : Fin C.pair.dimension) ≤ i from hi)).trans htarget
  obtain ⟨E,hEm,hEp,hE⟩ := gaussian_chebyshev_strong_filter_good_event T source Sinv hs hr.le hleft
    a (mainConditionBound I) I.singleFailure I.alpha hk ha hInv hcond hU I.singleFailure_positive
    I.singleFailure_le_one I.alpha_positive I.alpha_le_one hd.1 hd.2 htail
  refine ⟨E,hEm,hEp,?_⟩
  intro G hG
  have hK : Kᵀ=K := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (mainTruePencil_isHermitian I S C t.val).eq
  have hp := physicalStrongSuccess_of_core (supportLeftFactor I.A S.initialA C.pair) R K T source
    I.alpha I.alpha_positive.le _ hf.isUnit hK rfl G (hE G hG)
  have hy : mainStrongPhysicalPolynomial kernels I S C hk t =
      (fun G => supportLeftFactor I.A S.initialA C.pair*((R⁻¹)ᵀ*
        strongGaussianOutput T source I.alpha (strongGaussianDegree C.pair.dimension
          (mainConditionBound I) I.singleFailure I.alpha hk hU I.singleFailure_positive
          I.singleFailure_le_one I.alpha_positive I.alpha_le_one) G)) := by
    funext G
    unfold mainStrongPhysicalPolynomial
    exact (mainPhysicalPolynomial_eq_lift I S C t.val base hf.isUnit I.alpha _ G).trans
      (Matrix.mul_assoc _ _ _)
  rw [hy]
  exact hp

end
end HierarchicalAbsoluteSpectral
