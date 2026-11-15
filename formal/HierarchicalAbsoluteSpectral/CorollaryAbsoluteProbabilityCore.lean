import HierarchicalAbsoluteSpectral.MainStrongProbability
import HierarchicalAbsoluteSpectral.MainStatementsRitzProbability
import HierarchicalAbsoluteSpectral.ProbabilityJointInertiaProgram
import HierarchicalAbsoluteSpectral.MainSketchCommon

/-! Fixed-threshold probability tools with an attempted rank independent of
`FixedProblem`'s positive seed rank. In particular the attempted rank may be
zero. The no-false-advance lemma holds for every random tape, including
exceptional inertia tapes. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L k s : ℕ}

theorem decisionOfOptionalTests_ne_below {N : ℕ} {values : Fin N → ℝ} {ε : ℝ}
    (tests : ∀ i, Option (CertifiedRitzTests (values i) ε))
    (hvalues : ∀ i, values i ≤ 1) : decisionOfOptionalTests tests ≠ .below := by
  classical
  unfold decisionOfOptionalTests
  split_ifs with hn
  · exact ThresholdDecision.noConfusion
  · rw [decisionOfCertifiedTests_eq]
    unfold thresholdDecision
    have hnot : ¬ ∃ i, 1 < values i := by
      rintro ⟨i,hi⟩
      exact (not_lt_of_ge (hvalues i)) hi
    rw [if_neg hnot]
    split_ifs <;> exact ThresholdDecision.noConfusion

theorem repeatedKrylovQueryProgram_ne_below_of_target
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ s) (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin s → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ)
    (htarget : orderedEigenvalue T hT.isHermitian j ≤ 1) :
    (repeatedKrylovQueryProgram kernels T hT.isHermitian actions q S source j ε N G g).eval ≠
      .below := by
  simp only [repeatedKrylovQueryProgram,eval_bind,dependentTabulate_eval,eval_pure]
  apply decisionOfOptionalTests_ne_below
  intro i
  have hb := computedKrylovRitzValue_always_safe kernels T hT actions q S (G i) j
  have hn := orderedEigenvalue_nonneg T hT j
  have hs : (orderedEigenvalue T hT.isHermitian j)^2 ≤ 1 := by nlinarith
  exact hb.trans hs

/-- The same actual carried polynomial as in the main strong program, with
an independent attempted rank. It also defines the empty-column output. -/
def absoluteStrongPhysicalPolynomial
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) : Matrix (Fin n) (Fin s) ℝ :=
  let base := mainStrongBase kernels I S C t
  let v := strongGaussianDegree C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha hk
    (mainConditionBound_ge_one I) I.singleFailure_positive I.singleFailure_le_one I.alpha_positive I.alpha_le_one
  (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
    (aeval (mainCarriedMatrix I S C t.val base) (strongFilterPolynomial I.alpha v)*columnsMatrix G)

theorem absoluteStrongPhysicalPolynomial_eq_automatic
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    let base := mainStrongBase kernels I S C t
    absoluteStrongPhysicalPolynomial kernels I S C s hk t G =
      (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
        (aeval (mainCarriedMatrix I S C t.val base) (strongFilterPolynomial I.alpha
          (automaticStrongPhysicalRangeProgram kernels (mainCarriedAction kernels I S C t.val base s)
            (mainPhysicalMapAction kernels I S C t.val base s) (mainConditionBound I)
            I.singleFailure I.alpha hk (mainConditionBound_ge_one I) I.singleFailure_positive
            I.singleFailure_le_one I.alpha_positive I.alpha_le_one (columnsMatrix G)).eval.1)*columnsMatrix G) := by
  dsimp only
  rw [automaticStrongPhysicalRangeProgram_degree]
  rfl

theorem absolutePhysicalPolynomial_eq_lift
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t)
    (hR : IsUnit (mainRefinedFactor I S C t base).det) (α : ℝ) (v : ℕ)
    (G : Fin s → Fin C.pair.dimension → ℝ) :
    (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
      (aeval (mainCarriedMatrix I S C t base) (strongFilterPolynomial α v)*columnsMatrix G) =
    supportLeftFactor I.A S.initialA C.pair*((mainRefinedFactor I S C t base)⁻¹)ᵀ*
      strongGaussianOutput (mainThresholdOperator I S C t base) (mainSourceFactor I S C t base) α v G := by
  have hh := exact_physical_lift (supportLeftFactor I.A S.initialA C.pair) base.inverseFactor
    (mainSourceFactor I S C t base) (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)
    (mainSourceFactor_isUnit I S C t base hR) (strongFilterPolynomial α v) (columnsMatrix G)
  rw [mainBase_mul_source,mainFilteredOperator_eq,← mainCarriedMatrix_eq,mainBase_inverse_eq_upper] at hh
  simpa only [strongGaussianOutput,Matrix.mul_assoc] using hh.symm

/-- A measurable strong event at a fixed threshold, including attempted
rank zero. Only the actual threshold operator's tail bound is required. -/
theorem MainSketchGood.absolute_strong_physical_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t})
    (htarget : orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨s,hs⟩ ≤ 1+I.alpha) :
    ∃ E : Set (Fin s → Fin C.pair.dimension → ℝ), MeasurableSet E ∧
      (gaussianColumns C.pair.dimension s).real E ≥ 1-I.singleFailure ∧
        ∀ G ∈ E, G ∈ physicalStrongSuccess (supportLeftFactor I.A S.initialA C.pair)
          (mainRefinedFactor I S C t.val (mainStrongBase kernels I S C t)) (mainTruePencil I S C t.val)
          (absoluteStrongPhysicalPolynomial kernels I S C s hk t) I.alpha := by
  let base := mainStrongBase kernels I S C t
  let R := mainRefinedFactor I S C t.val base
  let K := mainTruePencil I S C t.val
  let T := mainThresholdOperator I S C t.val base
  let source := mainSourceFactor I S C t.val base
  let Sinv := R⁻¹*base.inverseFactor
  let a := (1+hierarchyUpper L/(8*I.accuracy 0))⁻¹
  let hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (mainThresholdOperator_isHermitian I S C t.val base)
  have hf := hg.actual_hierarchy kernels I S C t.val t.property
  have hb := hg.actual_threshold_bounds kernels I S C t.val t.property
  obtain ⟨hleft,ha,hInv,hSnorm,hRatio,hU⟩ := hg.actual_source_condition kernels I S C t.val t.property
  have hcond : ‖source‖/a ≤ mainConditionBound I :=
    (div_le_div_of_nonneg_right hSnorm ha.le).trans hRatio
  have hd := strongEigenvalues_bounds_of_order T hsym hb.1 hb.2
  have htail : ∀ i : Fin C.pair.dimension, s ≤ i.val → strongEigenvalues T hsym i ≤ 1+I.alpha := by
    intro i hi
    exact (hsym.eigenvalues_antitone (by simp) (show (⟨s,hs⟩ : Fin C.pair.dimension) ≤ i from hi)).trans htarget
  obtain ⟨E,hEm,hEp,hE⟩ := gaussian_chebyshev_strong_filter_good_event T source Sinv hsym hs.le hleft
    a (mainConditionBound I) I.singleFailure I.alpha hk ha hInv hcond hU I.singleFailure_positive
    I.singleFailure_le_one I.alpha_positive I.alpha_le_one hd.1 hd.2 htail
  refine ⟨E,hEm,hEp,?_⟩
  intro G hG
  have hK : Kᵀ=K := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (mainTruePencil_isHermitian I S C t.val).eq
  have hp := physicalStrongSuccess_of_core (supportLeftFactor I.A S.initialA C.pair) R K T source
    I.alpha I.alpha_positive.le _ hf.isUnit hK rfl G (hE G hG)
  have hy : absoluteStrongPhysicalPolynomial kernels I S C s hk t =
      (fun G => supportLeftFactor I.A S.initialA C.pair*((R⁻¹)ᵀ*
        strongGaussianOutput T source I.alpha (strongGaussianDegree C.pair.dimension
          (mainConditionBound I) I.singleFailure I.alpha hk hU I.singleFailure_positive
          I.singleFailure_le_one I.alpha_positive I.alpha_le_one) G)) := by
    funext G
    unfold absoluteStrongPhysicalPolynomial
    exact (absolutePhysicalPolynomial_eq_lift I S C t.val base hf.isUnit I.alpha _ G).trans
      (Matrix.mul_assoc _ _ _)
  rw [hy]
  exact hp

end
end HierarchicalAbsoluteSpectral
