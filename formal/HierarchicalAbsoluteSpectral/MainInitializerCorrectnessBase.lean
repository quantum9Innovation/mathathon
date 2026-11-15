import HierarchicalAbsoluteSpectral.MassSpectrumInitializer
import HierarchicalAbsoluteSpectral.MassSpectrumRoots
import HierarchicalAbsoluteSpectral.MainOperatorCorrectness
import HierarchicalAbsoluteSpectral.MainStatementsArrays
import HierarchicalAbsoluteSpectral.MainInitializerObservable

/-! Correctness of the initializer in the actual small-core program.  The
mass and its eigenvalues below are analytical proof objects.  The program
only evaluates its Gaussian range, Frobenius residual and scalar bracket.
No positive definiteness or simple-spectrum assumption is imposed on the
right Gram matrix or on the computed sketch. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def mainInitializerMass (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : Core C.pair.dimension :=
  constructedNeumannMass (mainTrueGram I S C) I.massAccuracy I.final_budget.mass_positive

def mainInitializerMassTarget (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) : ℝ :=
  massEigenvalue (mainTrueRightGram I S C) (mainInitializerMass I S C)
    (mainTrueRightGram_posSemidef I S C).isHermitian ⟨r,hr⟩

theorem mainInitializerMass_posDef (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    (mainInitializerMass I S C).PosDef := by
  have hG : (mainTrueGram I S C).IsHermitian := by
    rw [mainTrueGram_eq]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self
        (supportLeftFactor I.A S.initialA C.pair)).isHermitian
  exact constructedNeumannMass_posDef _ hG _ _

theorem MainSketchGood.initializer_mass_bands (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    (1/2 : ℝ) • (1 : Core C.pair.dimension) ≤ mainInitializerMass I S C ∧
      mainInitializerMass I S C ≤ (2 : ℝ) • (1 : Core C.pair.dimension) := by
  have hG := hg.normalized_gram_bounds I S C
  have hb := coarse_gram_inverse_bands (mainTrueGram I S C) (I.accuracy 0)
    (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le hG.1 hG.2
  have hm := constructedNeumannMass_relative (mainTrueGram I S C) hb.1
    I.massAccuracy I.final_budget.mass_positive hb.2.1 hb.2.2.1
  have he := base_mass_error (mainTrueGram I S C) (mainInitializerMass I S C)
    (I.accuracy 0) I.massAccuracy (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le
    I.final_budget.mass_positive.le (I.massAccuracy_le_level 0 (by omega)) hb.1
    hb.2.2.2.1 hb.2.2.2.2 hm.1 hm.2
  have hlo : (1-2*I.accuracy 0) • (1 : Core C.pair.dimension) ≤ mainInitializerMass I S C := by
    convert add_le_add_right he.1 (1 : Core C.pair.dimension) using 1 <;> module
  have hup : mainInitializerMass I S C ≤ (1+2*I.accuracy 0) • (1 : Core C.pair.dimension) := by
    convert add_le_add_right he.2 (1 : Core C.pair.dimension) using 1 <;> module
  exact ⟨(smul_le_smul_of_nonneg_right (by linarith [I.initial_accuracy_le] :
      (1/2 : ℝ) ≤ 1-2*I.accuracy 0) Matrix.PosSemidef.one.nonneg).trans hlo,
    hup.trans (smul_le_smul_of_nonneg_right (by linarith [I.initial_accuracy_le] :
      1+2*I.accuracy 0 ≤ (2 : ℝ)) Matrix.PosSemidef.one.nonneg)⟩

/-- The canonical mass target is within a factor four of the coarse
eigenvalue, with zero and repeated eigenvalues included. -/
theorem MainSketchGood.initializer_mass_comparison (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩/4 ≤
        mainInitializerMassTarget I S C hr ∧
      mainInitializerMassTarget I S C hr ≤
        4*orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ := by
  have hQ := mainTrueRightGram_posSemidef I S C
  have hq := hg.coarse_right_bounds I S C
  have hb := hg.initializer_mass_bands I S C
  have hmass := mainInitializerMass_posDef I S C
  have hlo : (1/2 : ℝ) • mainTrueRightGram I S C ≤ C.rightGram :=
    (smul_le_smul_of_nonneg_right (by linarith [I.initial_accuracy_le] :
      (1/2 : ℝ) ≤ 1-I.accuracy 0) hQ.nonneg).trans hq.1
  have hup : C.rightGram ≤ (2 : ℝ) • mainTrueRightGram I S C :=
    hq.2.trans (smul_le_smul_of_nonneg_right (by linarith [I.initial_accuracy_le] :
      1+I.accuracy 0 ≤ (2 : ℝ)) hQ.nonneg)
  have hh := HierarchicalAbsoluteSpectral.initializer_mass_comparison (mainTrueRightGram I S C) C.rightGram
    (massInverseFactor (mainInitializerMass I S C)) hQ C.rightGram_posSemidef.isHermitian
    (massInverseFactor_isUnit _ hmass) hlo hup
    (by rw [massInverseFactor_metric _ hmass]; exact hb.1)
    (by rw [massInverseFactor_metric _ hmass]; exact hb.2) ⟨r,hr⟩
  exact hh

theorem MainSketchGood.initializer_target_nonneg (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S)
    (hr : r < C.pair.dimension) : 0 ≤ mainInitializerMassTarget I S C hr := by
  have hh := hg.initializer_mass_comparison I S C hr
  have hp := orderedEigenvalue_nonneg C.rightGram C.rightGram_posSemidef ⟨r,hr⟩
  linarith

/-- The dimension-uniform budget used by `mainCoreProgram` dominates the
ratio computed using the actual support dimension, including dimension zero. -/
theorem initializerRatio_mono_dimension {k d : ℕ} (hkd : k ≤ d) (β : ℝ) (hβ : 0 < β) :
    initializerRatio k β ≤ initializerRatio d β := by
  unfold initializerRatio gaussianCaptureRadius
  gcongr

theorem InitializerComputation.exact_value_zero {k q : ℕ} {T : Core k}
    {Ξ : Matrix (Fin k) (Fin q) ℝ} {β : ℝ} (out : InitializerComputation T Ξ β)
    (hexact : out.result = .exact) : initializerValue T out.range.basis = 0 := by
  have ht : out.value ≤ 0 := by
    rw [out.result_eq] at hexact
    split_ifs at hexact with ht
    exact ht
  rw [out.value_eq] at ht
  exact le_antisymm ht (matrixFrobeniusValue_nonneg _)

theorem InitializerComputation.bracket_values {k q : ℕ} {T : Core k}
    {Ξ : Matrix (Fin k) (Fin q) ℝ} {β l u : ℝ} (out : InitializerComputation T Ξ β)
    (hbracket : out.result = .bracket l u) :
    0 < out.value ∧ l = out.value/initializerRatio k β ∧ u = out.value := by
  rw [out.result_eq] at hbracket
  split_ifs at hbracket with ht
  exact ⟨lt_of_not_ge ht,(InitializerResult.bracket.inj hbracket).1.symm,
    (InitializerResult.bracket.inj hbracket).2.symm⟩

/-- The computed zero branch reconstructs the original product exactly.
Only the actual branch test is assumed, with no successful-output certificate. -/
theorem MainSketchGood.initializer_exact_physical_output
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (Ξ : Matrix (Fin C.pair.dimension) (Fin r) ℝ)
    (hexact : (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval.result = .exact) :
    let out := (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval
    (exactPhysicalOutputProgram kernels I.A I.B
      (mainSupportAction kernels I S C out.range.dimension) out.range.basis
      out.range.dimension_le_cols).eval.product = I.A*I.B := by
  let out := (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval
  apply exactPhysicalOutputProgram_exact kernels I.A I.B
    (supportLeftFactor I.A S.initialA C.pair) (supportRightFactor S.initialA C.pair I.B)
    (hg.support_exact I S C) C.rightGram _ out.range.basis out.range.dimension_le_cols
    (1-I.accuracy 0) (by linarith [I.initial_accuracy_le])
  · rw [← mainTrueRightGram_eq]
    exact (hg.coarse_right_bounds I S C).1
  · exact out.exact_value_zero hexact

/-- Correctness of the actual positive initializer branch.  The widened
endpoints are exactly those passed to the counted threshold search. -/
theorem MainSketchGood.initializer_positive_bracket
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (Ξ : Matrix (Fin C.pair.dimension) (Fin r) ℝ) (l u : ℝ)
    (hbracket : (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval.result =
      .bracket l u)
    (hgood : let out := (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval
      orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ ≤ out.value ∧
      out.value ≤ initializerRatio C.pair.dimension I.singleFailure*
        orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩) :
    0 < l/4 ∧ l/4 ≤ mainInitializerMassTarget I S C hr ∧
      mainInitializerMassTarget I S C hr ≤ 4*u ∧
      (4*u)/(l/4) = 16*initializerRatio C.pair.dimension I.singleFailure ∧
      (4*u)/(l/4) ≤ 16*initializerRatio m I.singleFailure := by
  let out := (gaussianInitializerProgram kernels C.rightGram Ξ I.singleFailure).eval
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hC := initializerRatio_pos C.pair.dimension I.singleFailure (by omega) hβ
  obtain ⟨ht,hl,hu⟩ := out.bracket_values hbracket
  have hlpos : 0 < l := by rw [hl]; exact div_pos ht hC
  have hle : l ≤ orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ := by
    rw [hl]
    exact (div_le_iff₀ hC).mpr (by nlinarith [hgood.2])
  have hhi : orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ ≤ u := by
    rw [hu]
    exact hgood.1
  have hb := initializer_widened_mass_bracket _ _ l u hlpos hle hhi
    (hg.initializer_mass_comparison I S C hr)
  have hratio : u/l = initializerRatio C.pair.dimension I.singleFailure := by
    rw [hl,hu]
    field_simp
  have hw := initializer_widened_ratio l u _ hlpos hratio
  refine ⟨hb.1,hb.2.1,hb.2.2,hw,?_⟩
  rw [hw]
  exact mul_le_mul_of_nonneg_left
    (initializerRatio_mono_dimension (mainSupport_dimension_le S C) I.singleFailure hβ) (by norm_num)

/-- One measurable Gaussian event establishes the scalar inequalities for
the computed program, including cores whose target eigenvalue is zero. -/
theorem mainInitializer_computed_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    ∃ E : Set (Fin r → Fin C.pair.dimension → ℝ), MeasurableSet E ∧
      (gaussianColumns C.pair.dimension r).real E ≥ 1-I.singleFailure ∧ ∀ G ∈ E,
        let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval
        orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ ≤ out.value ∧
          out.value ≤ initializerRatio C.pair.dimension I.singleFailure*
            orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr C.rightGram_posSemidef.isHermitian
  have hd : ∀ i, 0 ≤ strongEigenvalues C.rightGram hs i :=
    fun i => orderedEigenvalue_nonneg C.rightGram C.rightGram_posSemidef i
  exact gaussian_initializer_program_good_event kernels C.rightGram hs hr hd I.singleFailure
    (div_pos I.delta_positive (by norm_num))
    (by dsimp [FixedProblem.singleFailure]; linarith [I.delta_lt_one])

/-- The event is a predicate on the actual computed value, rather than on
an uncomputed basis or a successful-output certificate. -/
def mainInitializerScalarGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    Set (Fin r → Fin C.pair.dimension → ℝ) :=
  {G | let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval
    orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ ≤ out.value ∧
      out.value ≤ initializerRatio C.pair.dimension I.singleFailure*
        orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩}

theorem mainInitializerScalarGood_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    MeasurableSet (mainInitializerScalarGood kernels I S C hr) := by
  have hm := gaussianInitializerProgram_value_gaussian_measurable (r:=r) kernels C.rightGram I.singleFailure
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

theorem mainInitializerScalarGood_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    (gaussianColumns C.pair.dimension r).real (mainInitializerScalarGood kernels I S C hr) ≥
      1-I.singleFailure := by
  obtain ⟨E,hEm,hEp,hE⟩ := mainInitializer_computed_good_event kernels I S C hr
  exact hEp.trans (measureReal_mono (fun G hG => hE G hG))

theorem MainSketchGood.initializer_zero_target_iff_exact
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (G : Fin r → Fin C.pair.dimension → ℝ)
    (hgood : G ∈ mainInitializerScalarGood kernels I S C hr) :
    mainInitializerMassTarget I S C hr = 0 ↔
      (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval.result = .exact := by
  let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval
  have hcompare := hg.initializer_mass_comparison I S C hr
  have hnonneg := hg.initializer_target_nonneg I S C hr
  have hcoarse_nonneg := orderedEigenvalue_nonneg C.rightGram C.rightGram_posSemidef ⟨r,hr⟩
  constructor
  · intro hz
    have hell : orderedEigenvalue C.rightGram C.rightGram_posSemidef.isHermitian ⟨r,hr⟩ = 0 := by
      linarith [hcompare.1]
    have ht : out.value ≤ 0 := by
      have hh := hgood.2
      rw [hell,mul_zero] at hh
      exact hh
    rw [out.result_eq,if_pos ht]
  · intro hexact
    have hz : out.value = 0 := out.value_eq.trans (out.exact_value_zero hexact)
    have hh := hgood.1
    change _ ≤ out.value at hh
    rw [hz] at hh
    linarith [hcompare.2]

/-- The complete initializer branch guarantee on its explicit measurable
event.  In the positive case the exact ratio is bounded by the original
dimension's uniform threshold-search budget. -/
theorem MainSketchGood.initializer_branch_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension)
    (G : Fin r → Fin C.pair.dimension → ℝ)
    (hgood : G ∈ mainInitializerScalarGood kernels I S C hr) :
    let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval
    match out.result with
    | .exact => (exactPhysicalOutputProgram kernels I.A I.B
        (mainSupportAction kernels I S C out.range.dimension) out.range.basis
        out.range.dimension_le_cols).eval.product = I.A*I.B
    | .bracket l u => 0 < l/4 ∧ l/4 ≤ mainInitializerMassTarget I S C hr ∧
        mainInitializerMassTarget I S C hr ≤ 4*u ∧
        (4*u)/(l/4) = 16*initializerRatio C.pair.dimension I.singleFailure ∧
        (4*u)/(l/4) ≤ 16*initializerRatio m I.singleFailure := by
  dsimp only
  cases hout : (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval.result with
  | exact => exact hg.initializer_exact_physical_output kernels I S C (columnsMatrix G) hout
  | bracket l u => exact hg.initializer_positive_bracket kernels I S C hr (columnsMatrix G) l u hout hgood

/-- The fixed stored sketches may be conditioned on before using this
event: the sole random input here is the independent initializer array. -/
theorem MainSketchGood.initializer_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    ∃ E : Set (Fin r → Fin C.pair.dimension → ℝ), MeasurableSet E ∧
      (gaussianColumns C.pair.dimension r).real E ≥ 1-I.singleFailure ∧ ∀ G ∈ E,
        let out := (gaussianInitializerProgram kernels C.rightGram (columnsMatrix G) I.singleFailure).eval
        (mainInitializerMassTarget I S C hr = 0 ↔ out.result = .exact) ∧
        match out.result with
        | .exact => (exactPhysicalOutputProgram kernels I.A I.B
            (mainSupportAction kernels I S C out.range.dimension) out.range.basis
            out.range.dimension_le_cols).eval.product = I.A*I.B
        | .bracket l u => 0 < l/4 ∧ l/4 ≤ mainInitializerMassTarget I S C hr ∧
            mainInitializerMassTarget I S C hr ≤ 4*u ∧
            (4*u)/(l/4) = 16*initializerRatio C.pair.dimension I.singleFailure ∧
            (4*u)/(l/4) ≤ 16*initializerRatio m I.singleFailure := by
  refine ⟨mainInitializerScalarGood kernels I S C hr,
    mainInitializerScalarGood_measurable kernels I S C hr,
    mainInitializerScalarGood_probability kernels I S C hr,?_⟩
  intro G hG
  exact ⟨hg.initializer_zero_target_iff_exact kernels I S C hr G hG,
    hg.initializer_branch_correct kernels I S C hr G hG⟩

theorem mainInitializerScalarGood_tape_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (hr : r < C.pair.dimension) :
    MeasurableSet {g : MainRandomTape I |
      mainInitializerArray I S C g ∈ mainInitializerScalarGood kernels I S C hr} ∧
      (mainRandomLaw I).real {g : MainRandomTape I |
        mainInitializerArray I S C g ∈ mainInitializerScalarGood kernels I S C hr} ≥
        1-I.singleFailure := by
  have hm := mainInitializerScalarGood_measurable kernels I S C hr
  have hp := mainInitializerArray_measurePreserving I S C
  refine ⟨hm.preimage hp.measurable,?_⟩
  change (mainRandomLaw I).real
    (mainInitializerArray I S C ⁻¹' mainInitializerScalarGood kernels I S C hr) ≥ _
  rw [hp.measureReal_preimage hm.nullMeasurableSet]
  exact mainInitializerScalarGood_probability kernels I S C hr

end
end HierarchicalAbsoluteSpectral
