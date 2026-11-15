import HierarchicalAbsoluteSpectral.MainStrongProbabilityEvent

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem mainStrongThresholdProgram_good_event (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t})
    (htarget : orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨r,hr⟩ ≤ 1+I.alpha)
    (htail : t.val ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
      (tailSingularValue (I.A*I.B) r)^2) :
    ∃ E : Set (Fin r → Fin C.pair.dimension → ℝ), MeasurableSet E ∧
      (gaussianColumns C.pair.dimension r).real E ≥ 1-I.singleFailure ∧ ∀ G ∈ E,
        let result := (mainStrongThresholdProgram kernels I S C hk t G).eval
        result.product.rank ≤ r ∧ ‖I.A*I.B-result.product‖ ≤ (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  let base := mainStrongBase kernels I S C t
  let Z := supportLeftFactor I.A S.initialA C.pair
  let Bbar := supportRightFactor S.initialA C.pair I.B
  let R := mainRefinedFactor I S C t.val base
  let Bm := constructedNeumannMass (mainTrueGram I S C) I.massAccuracy I.final_budget.mass_positive
  have hb := hg.gram_bands I S C
  have hGpos : (mainTrueGram I S C).PosDef := posDef_of_half_identity_le _ hb.1
  have hGsym := hGpos.isHermitian
  have hBm : Bmᵀ=Bm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (constructedNeumannMass_posDef _ hGsym I.massAccuracy I.final_budget.mass_positive).isHermitian.eq
  have hmass := (constructedNeumannMass_relative (mainTrueGram I S C) hGpos
    I.massAccuracy I.final_budget.mass_positive hb.1 hb.2).2
  have hGceil : mainTrueGram I S C ≤ (2 : ℝ) • (1 : Core C.pair.dimension) :=
    hb.2.trans (smul_le_smul_of_nonneg_right (by norm_num : (3/2 : ℝ) ≤ 2) Matrix.PosSemidef.one.nonneg)
  have htrue : mainTrueGram I S C=Zᵀ*Z := mainTrueGram_eq I S C
  have hright : mainTrueRightGram I S C=Bbar*Bbarᵀ := mainTrueRightGram_eq I S C
  have hQ := (hg.right_gram_comparison I S C).2
  rw [hright] at hQ
  have hf := hg.actual_hierarchy kernels I S C t.val t.property
  have hK : mainTruePencil I S C t.val=t.val • Bm-Bbar*Bbarᵀ := by
    simp only [mainTruePencil,trueNeumannPencil,Bm,hright]
  have hinvariant : inverseMetric R-hierarchyRelaxation L •
      ((t.val • Bm-Bbar*Bbarᵀ)*(inverseMetric R)⁻¹*(t.val • Bm-Bbar*Bbarᵀ)) ≤
        (hierarchyConstant L*I.accuracy L) • (t.val • (1 : Core C.pair.dimension)+C.rightGram) := by
    simpa only [hK] using hf.defect
  obtain ⟨E,hEm,hEp,hE⟩ := mainStrongPhysicalPolynomial_good_event kernels I S hg C hr hk t htarget
  refine ⟨E,hEm,hEp,?_⟩
  intro G hG
  have hStrong := hE G hG
  have hy : mainStrongPhysicalPolynomial kernels I S C hk t =
      (fun G' => (Z*base.metricFactor.upperᵀ)*
        (aeval (mainCarriedMatrix I S C t.val base) (strongFilterPolynomial I.alpha
          (automaticStrongPhysicalRangeProgram kernels (mainCarriedAction kernels I S C t.val base r)
            (mainPhysicalMapAction kernels I S C t.val base r) (mainConditionBound I)
            I.singleFailure I.alpha hk (mainConditionBound_ge_one I) I.singleFailure_positive
            I.singleFailure_le_one I.alpha_positive I.alpha_le_one (columnsMatrix G')).eval.1)*columnsMatrix G')) := by
    funext G'
    exact mainStrongPhysicalPolynomial_eq_automatic kernels I S C hk t G'
  rw [hy,hK] at hStrong
  have hθ1 : I.theta ≤ 1 := I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num))
  have hs := strongProjectionOutputProgram_error (k:=C.pair.dimension) (r:=r) kernels I.A I.B Z Bbar
    (hg.support_exact I S C) R Bm C.rightGram hf.isUnit hBm
    (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
    (hierarchyRelaxation L) (hierarchyConstant L) (I.accuracy L) I.theta t.val
    (mainConditionBound I) I.singleFailure (hierarchyRelaxation_bounds L).2 (hierarchyConstant_ge_one L)
    (I.accuracy_positive L le_rfl) I.theta_positive I.theta_le_last hθ1 t.property.le hk
    (mainConditionBound_ge_one I) I.singleFailure_positive I.singleFailure_le_one
    (by rw [← htrue]; exact hGpos) (by rw [← htrue]; exact hGceil) hQ
    (by
      change Bm ≤ (1+I.massAccuracy) • (Zᵀ*Z)⁻¹
      rw [← htrue]
      exact hmass) hinvariant htail G hStrong
  rw [mainStrongThresholdProgram_eval]
  exact hs

end
end HierarchicalAbsoluteSpectral
