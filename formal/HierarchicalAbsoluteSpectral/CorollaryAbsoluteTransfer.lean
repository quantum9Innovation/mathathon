import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProgram
import HierarchicalAbsoluteSpectral.MainStatementsTransfer
import HierarchicalAbsoluteSpectral.MassSpectrumSupport
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityCore
import HierarchicalAbsoluteSpectral.ThresholdMassDecision

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L k s : ℕ}

/-- Slack separation for the fixed absolute threshold. This is a scalar
lemma, not a test performed by the algorithm. -/
theorem absolute_threshold_slack (e θ ε a : ℝ)
    (he : 0 < e) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ/1000)
    (ha : 0 ≤ a) (hatail : a ≤ e/(1+θ)) :
    a^2/(1-ε) ≤ e^2/(1+θ/4) := by
  have hθp : 0 < 1+θ := by linarith
  have hεp : 0 < 1-ε := by linarith
  have htp : 0 < 1+θ/4 := by linarith
  have heθ : ε*θ ≤ ε := by nlinarith
  have hfirst : 1+θ/4 ≤ (1+θ)*(1-ε) := by nlinarith
  have hsecond : (1+θ)*(1-ε) ≤ (1+θ)^2*(1-ε) :=
    mul_le_mul_of_nonneg_right (by nlinarith : 1+θ ≤ (1+θ)^2) hεp.le
  have hsep := hfirst.trans hsecond
  have hs : a^2 ≤ (e/(1+θ))^2 := pow_le_pow_left₀ ha hatail 2
  calc
    a^2/(1-ε) ≤ (e/(1+θ))^2/(1-ε) := div_le_div_of_nonneg_right hs hεp.le
    _ = e^2/((1+θ)^2*(1-ε)) := by rw [div_pow,div_div]
    _ ≤ e^2/(1+θ/4) := div_le_div_of_nonneg_left (sq_nonneg e) htp hsep

theorem absolute_threshold_physical_budget (e θ u ε : ℝ)
    (he : 0 ≤ e) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : 0 ≤ u) (huθ : u ≤ θ/1000)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ/1000) :
    ((1+u+ε)/(1-u))*(e^2/(1+θ/4)) ≤ e^2 := by
  have hup : 0 < 1-u := by linarith
  have htp : 0 < 1+θ/4 := by linarith
  have huθ' : u*θ ≤ u := by nlinarith
  have hratio : (1+u+ε)/(1-u) ≤ 1+θ/4 := by
    apply (div_le_iff₀ hup).mpr
    nlinarith
  calc
    _ ≤ (1+θ/4)*(e^2/(1+θ/4)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = e^2 := by field_simp

/-- Absolute physical projection transfer, including rank zero. Unlike the
relative-error caller, no lower or upper target singular value is required. -/
theorem absolute_projection_error_of_certificate
    (M : Matrix (Fin n) (Fin p) ℝ) (U : Matrix (Fin n) (Fin s) ℝ)
    (hU : Uᵀ*U=1) (Z : Matrix (Fin n) (Fin k) ℝ) (F K D Bm : Core k)
    (κ C h b t ε θ e : ℝ)
    (hF : F.PosDef) (hK : Kᵀ=K)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (he : 0 ≤ e) (hκb : κ*b ≤ 1) (hu : b*C*h < 1)
    (hinvariant : F-κ • (K*F⁻¹*K) ≤ (C*h) • D)
    (hidentity : Z*K*Zᵀ=t • (Z*Bm*Zᵀ)-M*Mᵀ)
    (hmass : Z*Bm*Zᵀ ≤ (1+ε) • (1 : Core n))
    (hD : Z*D*Zᵀ ≤ (2*t) • (1 : Core n)+(2:ℝ) • (M*Mᵀ))
    (hstrong : ∀ x, Uᵀ*ᵥx=0 →
      quadratic (K*F⁻¹*K) (Zᵀ*ᵥx)-2*quadratic K (Zᵀ*ᵥx) ≤ b*quadratic F (Zᵀ*ᵥx))
    (hbudget : ((1+b*C*h+ε)/(1-b*C*h))*t ≤ e^2) :
    ‖M-U*(Uᵀ*M)‖ ≤ e := by
  apply projection_error_of_complement_bound M U hU e he
  intro x hx
  exact (physical_transfer_rayleigh M Z F K D Bm κ C h b t ε hF hK hb hC hh ht hκb hu
    hinvariant hidentity hmass hD x (hstrong x hx)).trans
      (mul_le_mul_of_nonneg_right hbudget (quadratic_nonneg Matrix.PosSemidef.one x))

def absoluteMass (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : Core C.pair.dimension :=
  constructedNeumannMass (mainTrueGram I S C) I.massAccuracy I.final_budget.mass_positive

def absoluteMassTarget (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) : ℝ :=
  massEigenvalue (mainTrueRightGram I S C) (absoluteMass I S C)
    (mainTrueRightGram_posSemidef I S C).isHermitian ⟨s,hs⟩

theorem absoluteMass_posDef (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : (absoluteMass I S C).PosDef := by
  have hG : (mainTrueGram I S C).IsHermitian := by
    rw [mainTrueGram_eq]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (supportLeftFactor I.A S.initialA C.pair)).isHermitian
  exact constructedNeumannMass_posDef _ hG _ _

theorem MainSketchGood.absolute_mass_target_upper
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) :
    absoluteMassTarget I S C s hs ≤ (tailSingularValue (I.A*I.B) s)^2/(1-I.massAccuracy) := by
  let Z := supportLeftFactor I.A S.initialA C.pair
  let Bbar := supportRightFactor S.initialA C.pair I.B
  have hb := hg.gram_bands I S C
  have hGpos : (mainTrueGram I S C).PosDef := posDef_of_half_identity_le _ hb.1
  have hrel := constructedNeumannMass_relative (mainTrueGram I S C) hGpos
    I.massAccuracy I.final_budget.mass_positive hb.1 hb.2
  have hε : I.massAccuracy < 1 := by
    have hθ := I.theta_le_last.trans ((I.accuracy_bounded L le_rfl).trans (by norm_num : (1/64:ℝ) ≤ 1))
    have hsmall := I.final_budget.mass_error
    change I.massAccuracy ≤ _ at hsmall
    linarith
  have htrue : mainTrueGram I S C=Zᵀ*Z := mainTrueGram_eq I S C
  have hright : mainTrueRightGram I S C=Bbar*Bbarᵀ := mainTrueRightGram_eq I S C
  have hsp : s < p := lt_of_lt_of_le hs ((mainSupport_dimension_le S C).trans I.core_le_cols)
  have hc := (support_approximate_mass_compare Z Bbar (absoluteMass I S C)
    (by rw [← htrue]; exact hGpos) (absoluteMass_posDef I S C)
    I.massAccuracy I.final_budget.mass_positive.le hε
    (by rw [← htrue]; exact hrel.1) (by rw [← htrue]; exact hrel.2) ⟨s,hs⟩ hsp).2
  change massEigenvalue (Bbar*Bbarᵀ) (absoluteMass I S C) _ ⟨s,hs⟩ ≤ _ at hc
  rw [← hg.support_exact I S C] at hc
  simpa only [absoluteMassTarget,hright] using hc

theorem MainSketchGood.absolute_mass_target_threshold
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension)
    (hslack : I.slackRank ≤ s) :
    absoluteMassTarget I.seed S C s hs ≤ absoluteThreshold I := by
  have hθ1 : I.theta ≤ 1 := I.seed.theta_le_last.trans
    ((I.seed.accuracy_bounded L le_rfl).trans (by norm_num))
  have htail : tailSingularValue (I.A*I.B) s ≤ I.tolerance/(1+I.theta) :=
    (tailSingularValue_antitone (I.A*I.B) hslack).trans
      (absoluteSlackRank_tail I.A I.B I.tolerance I.theta I.tolerance_positive I.theta_positive.le)
  exact (hg.absolute_mass_target_upper I.seed S C s hs).trans
    (absolute_threshold_slack I.tolerance I.theta I.seed.massAccuracy (tailSingularValue (I.A*I.B) s)
      I.tolerance_positive I.theta_positive hθ1 I.seed.final_budget.mass_positive.le
      I.seed.final_budget.mass_error (tailSingularValue_nonneg _ _) htail)

theorem MainSketchGood.absolute_threshold_target_le_one
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension)
    (hslack : I.slackRank ≤ s) :
    let t : {t : ℝ // 0 < t} := ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
    orderedEigenvalue (mainThresholdOperator I.seed S C t.val (mainStrongBase kernels I.seed S C t))
      (mainThresholdOperator_isHermitian I.seed S C t.val _) ⟨s,hs⟩ ≤ 1 := by
  dsimp only
  let t : {t : ℝ // 0 < t} := ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
  let R := mainRefinedFactor I.seed S C t.val (mainStrongBase kernels I.seed S C t)
  let Rb := massInverseFactor (absoluteMass I.seed S C)
  have hBm := absoluteMass_posDef I.seed S C
  have hRb := massInverseFactor_isUnit _ hBm
  have hR := (hg.actual_hierarchy kernels I.seed S C t.val t.property).isUnit
  have hmass : inverseMetric Rb=absoluteMass I.seed S C := massInverseFactor_metric _ hBm
  have htarget := hg.absolute_mass_target_threshold I S C s hs hslack
  have hfactor := massEigenvalue_eq_of_factor (mainTrueRightGram I.seed S C)
    (absoluteMass I.seed S C) Rb (mainTrueRightGram_posSemidef I.seed S C) hBm hRb hmass ⟨s,hs⟩
  have hq := mainTrueRightGram_posSemidef I.seed S C
  have ht : orderedEigenvalue (Rbᵀ*mainTrueRightGram I.seed S C*Rb)
      (normalized_isHermitian Rb _ hq.isHermitian.eq) ⟨s,hs⟩ ≤ t.val := by
    rw [← hfactor]
    exact htarget
  have hc : orderedEigenvalue (massThresholdOperator (mainTrueRightGram I.seed S C) R Rb t.val)
      (massThresholdOperator_isHermitian _ _ _ hq.isHermitian t.val) ⟨s,hs⟩ ≤ 1 := by
    by_contra hh
    have hb := (massThresholdOperator_below_iff (mainTrueRightGram I.seed S C) R Rb
      hq.isHermitian hR hRb t.val ⟨s,hs⟩).mp (lt_of_not_ge hh)
    exact (not_lt_of_ge ht) hb
  have hdef : mainThresholdOperator I.seed S C t.val (mainStrongBase kernels I.seed S C t)=
      massThresholdOperator (mainTrueRightGram I.seed S C) R Rb t.val := by
    simp only [mainThresholdOperator,massThresholdOperator,normalizedPencil,mainTruePencil,
      trueNeumannPencil,hmass,R,absoluteMass]
  change orderedEigenvalue (mainThresholdOperator I.seed S C t.val (mainStrongBase kernels I.seed S C t))
    (mainThresholdOperator_isHermitian I.seed S C t.val _) ⟨s,hs⟩ ≤ 1
  have heig : orderedEigenvalue
      (mainThresholdOperator I.seed S C t.val (mainStrongBase kernels I.seed S C t))
      (mainThresholdOperator_isHermitian I.seed S C t.val _) ⟨s,hs⟩ =
      orderedEigenvalue (massThresholdOperator (mainTrueRightGram I.seed S C) R Rb t.val)
        (massThresholdOperator_isHermitian _ _ _ hq.isHermitian t.val) ⟨s,hs⟩ := by
    congr 1
  exact heig.trans_le hc

theorem absoluteStrongThresholdProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    let base := mainStrongBase kernels I S C t
    (absoluteStrongThresholdProgram kernels I S C s hk t G).eval =
      (strongProjectionOutputProgram kernels I.A I.B
        (mainCarriedAction kernels I S C t.val base s) (mainPhysicalMapAction kernels I S C t.val base s)
        (mainConditionBound I) I.singleFailure I.alpha hk (mainConditionBound_ge_one I)
        I.singleFailure_positive I.singleFailure_le_one I.alpha_positive I.alpha_le_one (columnsMatrix G)).eval := by
  have hc : (mainConditionProgram I).certify.eval =
      ⟨mainConditionBound I,(mainConditionProgram_eval I).symm⟩ :=
    Subtype.ext ((ArithmeticProgram.certify_eval _).trans (mainConditionProgram_eval I))
  unfold absoluteStrongThresholdProgram
  simp only [ArithmeticProgram.eval_bind]
  erw [hc]

/-- The actual fresh carried-filter output meets the supplied absolute
tolerance on its constructed physical event, also at attempted rank zero. -/
theorem MainSketchGood.absolute_strong_output_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (s : ℕ) (hk : 1 ≤ C.pair.dimension)
    (G : Fin s → Fin C.pair.dimension → ℝ)
    (hStrong : G ∈ physicalStrongSuccess (supportLeftFactor I.A S.initialA C.pair)
      (mainRefinedFactor I.seed S C (absoluteThreshold I)
        (mainStrongBase kernels I.seed S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩))
      (mainTruePencil I.seed S C (absoluteThreshold I))
      (absoluteStrongPhysicalPolynomial kernels I.seed S C s hk
        ⟨absoluteThreshold I,absoluteThreshold_positive I⟩) I.seed.alpha) :
    ‖I.A*I.B-(absoluteStrongThresholdProgram kernels I.seed S C s hk
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ G).eval.product‖ ≤ I.tolerance := by
  let J := I.seed
  let t : {t : ℝ // 0 < t} := ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
  let base := mainStrongBase kernels J S C t
  let Z := supportLeftFactor I.A S.initialA C.pair
  let Bbar := supportRightFactor S.initialA C.pair I.B
  let R := mainRefinedFactor J S C t.val base
  let Bm := absoluteMass J S C
  let α := J.alpha
  let out := (strongProjectionOutputProgram kernels I.A I.B
    (mainCarriedAction kernels J S C t.val base s) (mainPhysicalMapAction kernels J S C t.val base s)
    (mainConditionBound J) J.singleFailure α hk (mainConditionBound_ge_one J)
    J.singleFailure_positive J.singleFailure_le_one J.alpha_positive J.alpha_le_one (columnsMatrix G)).eval
  have hy : absoluteStrongPhysicalPolynomial kernels J S C s hk t =
      (fun G' => (Z*base.metricFactor.upperᵀ)*
        (Polynomial.aeval (mainCarriedMatrix J S C t.val base) (strongFilterPolynomial α
          (automaticStrongPhysicalRangeProgram kernels (mainCarriedAction kernels J S C t.val base s)
            (mainPhysicalMapAction kernels J S C t.val base s) (mainConditionBound J)
            J.singleFailure α hk (mainConditionBound_ge_one J) J.singleFailure_positive
            J.singleFailure_le_one J.alpha_positive J.alpha_le_one (columnsMatrix G')).eval.1)*columnsMatrix G')) := by
    funext G'
    exact absoluteStrongPhysicalPolynomial_eq_automatic kernels J S C s hk t G'
  rw [hy] at hStrong
  have hc := strongProjectionOutputProgram_dual_certificate kernels I.A I.B
    (mainCarriedAction kernels J S C t.val base s) (mainPhysicalMapAction kernels J S C t.val base s)
    (mainConditionBound J) J.singleFailure α hk (mainConditionBound_ge_one J)
    J.singleFailure_positive J.singleFailure_le_one J.alpha_positive J.alpha_le_one
    Z R (mainTruePencil J S C t.val) G hStrong
  have hb := hg.gram_bands J S C
  have hGpos : (mainTrueGram J S C).PosDef := posDef_of_half_identity_le _ hb.1
  have htrue : mainTrueGram J S C=Zᵀ*Z := mainTrueGram_eq J S C
  have hright : mainTrueRightGram J S C=Bbar*Bbarᵀ := mainTrueRightGram_eq J S C
  have hmass := (constructedNeumannMass_relative (mainTrueGram J S C) hGpos
    J.massAccuracy J.final_budget.mass_positive hb.1 hb.2).2
  have hphysicalMass := physical_mass_bound Z Bm J.massAccuracy J.final_budget.mass_positive.le
    (by rw [← htrue]; exact hGpos) (by rw [← htrue]; exact hmass)
  have hGceil : Zᵀ*Z ≤ (2 : ℝ) • (1 : Core C.pair.dimension) := by
    rw [← htrue]
    exact hb.2.trans (smul_le_smul_of_nonneg_right (by norm_num : (3/2 : ℝ) ≤ 2) Matrix.PosSemidef.one.nonneg)
  have hQ := (hg.right_gram_comparison J S C).2
  rw [hright] at hQ
  have hphysicalD := physical_D_bound Z Bbar C.rightGram t.val t.property.le hGceil hQ
  have hidentity := physical_pencil_identity Z Bbar Bm t.val
  have hsupp : I.A*I.B=Z*Bbar := hg.support_exact J S C
  rw [← hsupp] at hphysicalD hidentity
  have hK : mainTruePencil J S C t.val=t.val • Bm-Bbar*Bbarᵀ := by
    simp only [mainTruePencil,trueNeumannPencil,Bm,absoluteMass,hright]
  have hKT : (mainTruePencil J S C t.val)ᵀ=mainTruePencil J S C t.val := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (mainTruePencil_isHermitian J S C t.val).eq
  have hf := hg.actual_hierarchy kernels J S C t.val t.property
  have hθ1 : I.theta ≤ 1 := J.theta_le_last.trans ((J.accuracy_bounded L le_rfl).trans (by norm_num))
  have hθJ : J.theta ≤ 1 := hθ1
  have hu := J.final_budget.physical_error
  have hu0 := J.final_budget.physical_nonneg
  have heps := J.final_budget.mass_error
  have hbudget : ((1+literalFinalB (hierarchyConstant L) (J.accuracy L) J.theta*
      hierarchyConstant L*J.accuracy L+J.massAccuracy)/
      (1-literalFinalB (hierarchyConstant L) (J.accuracy L) J.theta*hierarchyConstant L*J.accuracy L))*t.val ≤ I.tolerance^2 :=
    absolute_threshold_physical_budget I.tolerance I.theta
      (literalFinalU (hierarchyConstant L) (J.accuracy L) J.theta) J.massAccuracy
      I.tolerance_positive.le I.theta_positive.le hθ1 hu0 hu J.final_budget.mass_positive.le heps
  have herr := absolute_projection_error_of_certificate (I.A*I.B) out.left hc.1 Z
    (inverseMetric R) (mainTruePencil J S C t.val) (t.val • (1 : Core C.pair.dimension)+C.rightGram) Bm
    (hierarchyRelaxation L) (hierarchyConstant L) (J.accuracy L)
    (literalFinalB (hierarchyConstant L) (J.accuracy L) J.theta) t.val J.massAccuracy I.theta I.tolerance
    (inverseMetric_posDef R hf.isUnit) hKT J.final_budget.strong_nonneg
    (by have := hierarchyConstant_ge_one L; linarith) (J.accuracy_positive L le_rfl).le t.property.le
    I.tolerance_positive.le (J.final_budget.relaxation _ (hierarchyRelaxation_bounds L).2)
    (by change literalFinalU _ _ _ < 1; linarith only [hu,hθJ]) hf.defect
    (by rw [hK]; exact hidentity) hphysicalMass hphysicalD hc.2 hbudget
  have hp := strongProjectionOutputProgram_projected_product kernels I.A I.B
    (mainCarriedAction kernels J S C t.val base s) (mainPhysicalMapAction kernels J S C t.val base s)
    (mainConditionBound J) J.singleFailure α hk (mainConditionBound_ge_one J)
    J.singleFailure_positive J.singleFailure_le_one J.alpha_positive J.alpha_le_one (columnsMatrix G)
  change out.product=out.left*(out.leftᵀ*(I.A*I.B)) at hp
  rw [absoluteStrongThresholdProgram_eval]
  change ‖I.A*I.B-out.product‖ ≤ I.tolerance
  rw [hp]
  exact herr

end
end HierarchicalAbsoluteSpectral
