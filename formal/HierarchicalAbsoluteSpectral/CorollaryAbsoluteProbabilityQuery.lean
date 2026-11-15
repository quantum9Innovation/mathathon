import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityCore
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProgram

/-! Measurable fixed-threshold events for the actual arbitrary-rank query.
The attempted rank is independent of the seed rank and may be zero. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial Set
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L k s N : ℕ}
local instance absoluteQueryMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance absoluteQueryMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

/-- The degree depends on support dimension and accuracy, rather than on
the positive rank used to store the hierarchy's input parameters. -/
def absoluteKrylovDegree (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) : ℕ :=
  krylovDegree C.pair.dimension (mainConditionBound I) (1/2) (mainRitzAccuracy I)
    hk (mainConditionBound_ge_one I) (by norm_num) (by norm_num)
    (mainRitzAccuracy_positive I) (mainRitzAccuracy_le_one I)

theorem absolutePositiveQueryProgram_eval_repeated
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (hs : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (absolutePositiveQueryProgram kernels I S C s hs t G g).eval =
      (repeatedKrylovQueryProgram kernels
        (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
        (mainThresholdOperator_isHermitian I S C t.val _)
        (fun b => (mainThresholdAction kernels I S C t.val (mainStrongBase kernels I S C t) (s+1)).columnBlocks (by omega) b)
        (absoluteKrylovDegree I S C (by omega)) (mainSourceFactor I S C t.val (mainStrongBase kernels I S C t))
        (mainSourceAction kernels I S C t.val (mainStrongBase kernels I S C t) (s+1))
        ⟨s,hs⟩ (mainRitzAccuracy I) I.repetitions G g).eval := by
  simp only [absolutePositiveQueryProgram,eval_bind]
  simp only [certify_eval,mainConditionProgram_eval,eval_div]
  exact automaticKrylovQueryProgram_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- At or above the mass target, the executed query cannot falsely request
another rank, on any random tape. Failed inertia calls return `near`. -/
theorem MainSketchGood.absolute_query_no_false_advance
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (s : ℕ) (hs : s < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (s+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ)
    (htarget : orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨s,hs⟩ ≤ 1) :
    (absolutePositiveQueryProgram kernels I S C s hs t G g).eval ≠ .below := by
  rw [absolutePositiveQueryProgram_eval_repeated]
  exact repeatedKrylovQueryProgram_ne_below_of_target kernels _
    (hg.actual_threshold_bounds kernels I S C t.val t.property).1 _ _ _ _ _ _ _ _ _ htarget

abbrev AbsoluteQuerySamples (k s N : ℕ) := Fin N → Fin (s+1) → Fin k → ℝ
abbrev AbsoluteInertiaSamples (k N : ℕ) := Fin N → Fin 2 → Fin (k*k) → ℝ

def absoluteInertiaLaw (k N : ℕ) : Measure (AbsoluteInertiaSamples k N) :=
  Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)))

instance absoluteInertiaLaw_isProbability (k N : ℕ) : IsProbabilityMeasure (absoluteInertiaLaw k N) := by
  unfold absoluteInertiaLaw
  infer_instance

/-- Joint inertia success for both shifts and all repetitions at one fixed
threshold. The matrices depend on query samples, never inertia samples. -/
def absoluteFixedInertiaGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (S : Core k) (ε : ℝ)
    (G : AbsoluteQuerySamples k s N) (g : AbsoluteInertiaSamples k N) : Prop :=
  ∀ trial : Fin N,
    jointInertiaGood (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix (G trial))-(1 : ℝ) • (1 : Core k)) (g trial 0) ∧
    jointInertiaGood (krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix (G trial))-
      (1-2*ε) • (1 : Core k)) (g trial 1)

theorem absoluteFixedInertiaGood_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (S : Core k) (ε : ℝ) :
    MeasurableSet {z : AbsoluteQuerySamples k s N × AbsoluteInertiaSamples k N |
      absoluteFixedInertiaGood kernels T q S ε z.1 z.2} := by
  simp only [absoluteFixedInertiaGood,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro trial
  have hcols : Measurable (fun z : AbsoluteQuerySamples k s N × AbsoluteInertiaSamples k N =>
      Sᵀ*columnsMatrix (z.1 trial)) :=
    (continuous_const.matrix_mul continuous_id).measurable.comp
      (columnsMatrix_continuous.measurable.comp
        ((measurable_pi_apply trial).comp measurable_fst))
  have hM : Measurable (fun z : AbsoluteQuerySamples k s N × AbsoluteInertiaSamples k N =>
      krylovRitzFixedMatrix kernels T q (Sᵀ*columnsMatrix (z.1 trial))) :=
    (krylovRitzFixedMatrix_measurable kernels q).comp (measurable_const.prodMk hcols)
  exact (jointInertiaGood_measurable_comp _ _ (hM.sub measurable_const)
    ((measurable_pi_apply 0).comp ((measurable_pi_apply trial).comp measurable_snd))).inter
    (jointInertiaGood_measurable_comp _ _ (hM.sub measurable_const)
      ((measurable_pi_apply 1).comp ((measurable_pi_apply trial).comp measurable_snd)))

theorem absoluteFixedInertiaGood_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (S : Core k) (ε : ℝ) (G : AbsoluteQuerySamples k s N) :
    ∀ᵐ g ∂absoluteInertiaLaw k N, absoluteFixedInertiaGood kernels T q S ε G g := by
  apply ae_all_iff.mpr
  intro trial
  have heval (test : Fin 2) :=
    (measurePreserving_eval (fun _ : Fin 2 => gaussianVector (k*k)) test).comp
      (measurePreserving_eval (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => gaussianVector (k*k))) trial)
  exact (heval 0).quasiMeasurePreserving.ae (jointInertiaGood_ae _) |>.and
    ((heval 1).quasiMeasurePreserving.ae (jointInertiaGood_ae _))

theorem absoluteFixedInertiaGood_prod_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (q : ℕ) (S : Core k) (ε : ℝ) :
    ∀ᵐ z ∂(repeatedGaussianColumns k (s+1) N).prod (absoluteInertiaLaw k N),
      absoluteFixedInertiaGood kernels T q S ε z.1 z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (absoluteFixedInertiaGood_measurable kernels T q S ε)).mpr
  exact Filter.Eventually.of_forall (absoluteFixedInertiaGood_ae kernels T q S ε)

/-- At a fixed threshold, safe executed decisions hold on a measurable
query/inertia event with the repeated Ritz failure budget. -/
theorem repeatedKrylovQueryProgram_fixed_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (S Sinv : Core k) (hSinv : Sinv*S = 1) (j : Fin k)
    (a b U β ε : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hS : ‖S‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1/4) (q : ℕ)
    (hstop : 10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100) q)
    (N : ℕ) (source : MatrixAction Sᵀ (j.val+1)) :
    ∃ E : Set (AbsoluteQuerySamples k j.val N × AbsoluteInertiaSamples k N), MeasurableSet E ∧
      ((repeatedGaussianColumns k (j.val+1) N).prod (absoluteInertiaLaw k N)).real E ≥ 1-β^N ∧
      ∀ z ∈ E, ThresholdDecisionSafe (orderedEigenvalue T hT.isHermitian j) ε
        (repeatedKrylovQueryProgram kernels T hT.isHermitian actions q S source j ε N z.1 z.2).eval := by
  let R : Set (AbsoluteQuerySamples k j.val N) :=
    {G | ((⟨T,hT.isHermitian⟩,S),G) ∈ ritzRepeatedFailureSet kernels q j ε N}ᶜ
  let J : Set (AbsoluteQuerySamples k j.val N × AbsoluteInertiaSamples k N) :=
    {z | absoluteFixedInertiaGood kernels T q S ε z.1 z.2}
  let μ := (repeatedGaussianColumns k (j.val+1) N).prod (absoluteInertiaLaw k N)
  have hRm : MeasurableSet R :=
    ((ritzRepeatedFailureSet_measurable kernels q j ε N).preimage (measurable_const.prodMk measurable_id)).compl
  have hRp : (repeatedGaussianColumns k (j.val+1) N).real R ≥ 1-β^N := by
    have hh := ritzRepeatedFailureSet_fiber_probability kernels T hT actions S Sinv hSinv j
      a b U β ε ha hInv hS hba hU hβ hβ' hε (by linarith) q hstop N
    dsimp only [R]
    rw [measureReal_compl (by
      exact (ritzRepeatedFailureSet_measurable kernels q j ε N).preimage
        (measurable_const.prodMk measurable_id)),probReal_univ]
    linarith
  have hJm : MeasurableSet J := absoluteFixedInertiaGood_measurable kernels T q S ε
  have hJae : ∀ᵐ z ∂μ, z ∈ J := absoluteFixedInertiaGood_prod_ae kernels T q S ε
  let E : Set (AbsoluteQuerySamples k j.val N × AbsoluteInertiaSamples k N) := (Prod.fst ⁻¹' R) ∩ J
  have hEq : E =ᵐ[μ] (Prod.fst ⁻¹' R) := by
    filter_upwards [hJae] with z hz
    change ((z ∈ Prod.fst ⁻¹' R) ∧ z ∈ J) = (z ∈ Prod.fst ⁻¹' R)
    exact propext (and_iff_left hz)
  refine ⟨E,(hRm.preimage measurable_fst).inter hJm,?_,?_⟩
  · change μ.real E ≥ _
    rw [measureReal_congr hEq]
    rw [measurePreserving_fst.measureReal_preimage hRm.nullMeasurableSet]
    exact hRp
  · intro z hz
    apply repeatedKrylovQueryProgram_safe_of_events kernels T hT actions q S source j ε hε hε' N z.1 z.2
    · intro trial
      exact jointInertiaGood_polynomial_event _ _ (hz.2 trial).1
    · intro trial
      exact jointInertiaGood_polynomial_event _ _ (hz.2 trial).2
    · have hn := hz.1
      change ¬ ∀ trial, gaussianRitzObservable kernels q j ((⟨T,hT.isHermitian⟩,S),z.1 trial) <
        (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 at hn
      push Not at hn
      obtain ⟨trial,htrial⟩ := hn
      exact ⟨trial,by
        simpa only [gaussianRitzObservable_eq_computed kernels T hT.isHermitian actions] using htrial⟩

end
end HierarchicalAbsoluteSpectral
