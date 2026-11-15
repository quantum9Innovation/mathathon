import HierarchicalAbsoluteSpectral.MainSketchProbability
import HierarchicalAbsoluteSpectral.MainStatementsTapeLaw

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def mainLeftSketchEmbedding (I : FixedProblem n m p r L) (j : Fin (L+1)) :
    (Fin 3 × Fin (2^dyadicPaddingLevel n)) ↪ MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .sketchLeft j x.1 x.2
  inj' := by intro a b h; cases a; cases b; cases h; rfl

def mainRightSketchEmbedding (I : FixedProblem n m p r L) (j : Fin (L+1)) :
    (Fin 3 × Fin (2^dyadicPaddingLevel p)) ↪ MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .sketchRight j x.1 x.2
  inj' := by intro a b h; cases a; cases b; cases h; rfl

theorem mainLeftSketchInput_measurePreserving (I : FixedProblem n m p r L) (j : Fin (L+1)) :
    MeasurePreserving (fun g => mainLeftSketchInput I g j) (mainRandomLaw I)
      (gaussianSRHTInputLaw (dyadicPaddingLevel n)) := by
  simpa [mainLeftSketchInput,mainRandomLaw,gaussianSRHTInputLaw,mainLeftSketchEmbedding] using
    gaussianTape_threeBlocks_measurePreserving (2^dyadicPaddingLevel n) (mainLeftSketchEmbedding I j)

theorem mainRightSketchInput_measurePreserving (I : FixedProblem n m p r L) (j : Fin (L+1)) :
    MeasurePreserving (fun g => mainRightSketchInput I g j) (mainRandomLaw I)
      (gaussianSRHTInputLaw (dyadicPaddingLevel p)) := by
  simpa [mainRightSketchInput,mainRandomLaw,gaussianSRHTInputLaw,mainRightSketchEmbedding] using
    gaussianTape_threeBlocks_measurePreserving (2^dyadicPaddingLevel p) (mainRightSketchEmbedding I j)

theorem probability_finite_common_event {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ι → Set Ω) (β : ℝ)
    (hEm : ∀ i, MeasurableSet (E i)) (hEp : ∀ i, 1-β ≤ μ.real (E i)) :
    MeasurableSet {ω | ∀ i, ω ∈ E i} ∧
      1-(Fintype.card ι : ℝ)*β ≤ μ.real {ω | ∀ i, ω ∈ E i} := by
  classical
  let bad : Set Ω := ⋃ i, (E i)ᶜ
  have hbadm : MeasurableSet bad := MeasurableSet.iUnion (fun i => (hEm i).compl)
  have hbad : μ.real bad ≤ (Fintype.card ι : ℝ)*β := by
    calc
      _ ≤ ∑ i, μ.real ((E i)ᶜ) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : ι, β := by
        apply Finset.sum_le_sum
        intro i _
        have hh := hEp i
        rw [measureReal_compl (hEm i),probReal_univ]
        linarith
      _ = _ := by simp
  have he : {ω | ∀ i, ω ∈ E i} = badᶜ := by ext ω; simp [bad]
  rw [he]
  refine ⟨hbadm.compl,?_⟩
  rw [measureReal_compl hbadm,probReal_univ]
  linarith

theorem mainSketchProgram_good_event (I : FixedProblem n m p r L) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta/10 ∧
      ∀ g ∈ E, MainSketchGood I (mainSketchProgram I g).eval := by
  classical
  have hleft (j : Fin (L+1)) := boundedSketchProgram_good_event I.A (I.accuracy j.val) I.sketchFailure
    (I.accuracy_positive j.val (by omega)) (mainSketchAccuracy_le_one I j.val (by omega)) (mainSketchFailure_positive I)
  have hright (j : Fin (L+1)) := boundedSketchProgram_good_event I.Bᵀ (I.accuracy j.val) I.sketchFailure
    (I.accuracy_positive j.val (by omega)) (mainSketchAccuracy_le_one I j.val (by omega)) (mainSketchFailure_positive I)
  choose EA hEAm hEAp hEA using hleft
  choose EB hEBm hEBp hEB using hright
  let F : Fin (L+1) × Bool → Set (MainRandomTape I) := fun jb =>
    if jb.2 then (fun g => mainLeftSketchInput I g jb.1) ⁻¹' EA jb.1
    else (fun g => mainRightSketchInput I g jb.1) ⁻¹' EB jb.1
  have hFm : ∀ jb, MeasurableSet (F jb) := by
    rintro ⟨j,b⟩
    cases b
    · exact (hEBm j).preimage (mainRightSketchInput_measurePreserving I j).measurable
    · exact (hEAm j).preimage (mainLeftSketchInput_measurePreserving I j).measurable
  have hFp : ∀ jb, 1-I.sketchFailure ≤ (mainRandomLaw I).real (F jb) := by
    rintro ⟨j,b⟩
    cases b
    · have hp := mainRightSketchInput_measurePreserving I j
      have he : (mainRandomLaw I).real (F (j,false)) =
          (gaussianSRHTInputLaw (dyadicPaddingLevel p)).real (EB j) := by
        change ((mainRandomLaw I) ((fun g => mainRightSketchInput I g j) ⁻¹' EB j)).toReal = _
        rw [← hp.map_eq]
        change _ = ((Measure.map (fun g => mainRightSketchInput I g j) (mainRandomLaw I)) (EB j)).toReal
        rw [Measure.map_apply hp.measurable (hEBm j)]
      rw [he]
      exact hEBp j
    · have hp := mainLeftSketchInput_measurePreserving I j
      have he : (mainRandomLaw I).real (F (j,true)) =
          (gaussianSRHTInputLaw (dyadicPaddingLevel n)).real (EA j) := by
        change ((mainRandomLaw I) ((fun g => mainLeftSketchInput I g j) ⁻¹' EA j)).toReal = _
        rw [← hp.map_eq]
        change _ = ((Measure.map (fun g => mainLeftSketchInput I g j) (mainRandomLaw I)) (EA j)).toReal
        rw [Measure.map_apply hp.measurable (hEAm j)]
      rw [he]
      exact hEAp j
  have hc := probability_finite_common_event (mainRandomLaw I) F I.sketchFailure hFm hFp
  refine ⟨{g | ∀ jb, g ∈ F jb},hc.1,?_,?_⟩
  · have he : (Fintype.card (Fin (L+1) × Bool) : ℝ)*I.sketchFailure = I.delta/10 := by
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
        FixedProblem.sketchFailure]
      field_simp
      <;> ring
    simpa only [he] using hc.2
  · intro g hg j
    constructor
    · rw [mainSketchProgram_leftGram]
      exact hEA j (mainLeftSketchInput I g j) (hg (j,true))
    · rw [mainSketchProgram_rightGram]
      exact hEB j (mainRightSketchInput I g j) (hg (j,false))

end
end HierarchicalAbsoluteSpectral
