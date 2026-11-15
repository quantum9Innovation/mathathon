import HierarchicalAbsoluteSpectral.ProbabilityMainTapeDefs

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory
variable {n m p r L : ℕ}

instance mainSketchFiniteLaw_isProbability (I : FixedProblem n m p r L) :
    IsProbabilityMeasure ((mainRandomLaw I).map (mainSketchFiniteSample I)) :=
  Measure.isProbabilityMeasure_map (mainSketchFiniteSample_measurable I).aemeasurable

theorem gaussianFourSum_measurePreserving {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] :
    MeasurePreserving (fun g : A ⊕ (B ⊕ (C ⊕ D)) → ℝ =>
      ⟨(fun a => g (.inl a)), (fun b => g (.inr (.inl b))),
        (fun c => g (.inr (.inr (.inl c)))), (fun d => g (.inr (.inr (.inr d))))⟩)
      (Measure.pi (fun _ : A ⊕ (B ⊕ (C ⊕ D)) => gaussianReal 0 1))
      ((Measure.pi (fun _ : A => gaussianReal 0 1)).prod
        ((Measure.pi (fun _ : B => gaussianReal 0 1)).prod
          ((Measure.pi (fun _ : C => gaussianReal 0 1)).prod
            (Measure.pi (fun _ : D => gaussianReal 0 1))))) := by
  have hCD := gaussianSum_measurePreserving (A:=C) (B:=D)
  have hBCD := ((MeasurePreserving.id (Measure.pi (fun _ : B => gaussianReal 0 1))).prod hCD).comp
    (gaussianSum_measurePreserving (A:=B) (B:=C ⊕ D))
  exact ((MeasurePreserving.id (Measure.pi (fun _ : A => gaussianReal 0 1))).prod hBCD).comp
    (gaussianSum_measurePreserving (A:=A) (B:=B ⊕ (C ⊕ D)))

theorem mainCoreRawCurry_measurePreserving (I : FixedProblem n m p r L) :
    MeasurePreserving (mainCoreRawCurry I)
      (Measure.pi (fun _ : MainCoreRawIndex m r I.queryCap I.repetitions => gaussianReal 0 1))
      (mainCoreLawOriginal I) := by
  have hraw := gaussianFourSum_measurePreserving (A:=MainInitializerRawIndex m r)
    (B:=MainQueryRawIndex m r I.queryCap I.repetitions)
    (C:=MainInertiaRawIndex m I.queryCap I.repetitions) (D:=MainInitializerRawIndex m r)
  have hI := gaussianFiniteCurry_measurePreserving (A:=Fin r) (B:=Fin m)
  have hQ := gaussianTape_array4_measurePreserving
    (Function.Embedding.refl (MainQueryRawIndex m r I.queryCap I.repetitions))
  have hD := gaussianTape_array4_measurePreserving
    (Function.Embedding.refl (MainInertiaRawIndex m I.queryCap I.repetitions))
  exact (hI.prod (hQ.prod (hD.prod hI))).comp hraw

def mainTapeRawSplit (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (MainSketchRawIndex n p L → ℝ) × (MainCoreRawIndex m r I.queryCap I.repetitions → ℝ) :=
  ((fun i => g (mainTapePartition I (.inl i))), (fun i => g (mainTapePartition I (.inr i))))

theorem mainTapeRawSplit_measurePreserving (I : FixedProblem n m p r L) :
    MeasurePreserving (mainTapeRawSplit I) (mainRandomLaw I)
      ((Measure.pi (fun _ : MainSketchRawIndex n p L => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : MainCoreRawIndex m r I.queryCap I.repetitions => gaussianReal 0 1))) :=
  gaussianSum_measurePreserving.comp
    (gaussianTape_injection_measurePreserving (mainTapePartition I).toEmbedding)

/-- The finite preprocessing state is independent of every remaining original Gaussian array. -/
theorem mainSketchFiniteSample_coreTape_map (I : FixedProblem n m p r L) :
    (mainRandomLaw I).map (fun g => (mainSketchFiniteSample I g, mainCoreTapeOriginal I g)) =
      ((mainRandomLaw I).map (mainSketchFiniteSample I)).prod (mainCoreLawOriginal I) := by
  let μs := Measure.pi (fun _ : MainSketchRawIndex n p L => gaussianReal 0 1)
  let μc := Measure.pi (fun _ : MainCoreRawIndex m r I.queryCap I.repetitions => gaussianReal 0 1)
  have hs : MeasurePreserving (mainSketchRawSample I) μs (μs.map (mainSketchRawSample I)) :=
    ⟨mainSketchRawSample_measurable I,rfl⟩
  have hsplit := mainTapeRawSplit_measurePreserving I
  have hprod := (hs.prod (mainCoreRawCurry_measurePreserving I)).comp hsplit
  have hf := hs.comp ((measurePreserving_fst (μ:=μs) (ν:=μc)).comp hsplit)
  have hf' : (mainRandomLaw I).map (mainSketchFiniteSample I) = μs.map (mainSketchRawSample I) :=
    hf.map_eq
  calc
    _ = (μs.map (mainSketchRawSample I)).prod (mainCoreLawOriginal I) := hprod.map_eq
    _ = _ := by rw [hf']

theorem mainCoreTapeOriginal_measurable (I : FixedProblem n m p r L) :
    Measurable (mainCoreTapeOriginal I) := by
  unfold mainCoreTapeOriginal
  fun_prop

theorem mainSketchFiniteSample_coreTape_measurePreserving (I : FixedProblem n m p r L) :
    MeasurePreserving (fun g => (mainSketchFiniteSample I g, mainCoreTapeOriginal I g))
      (mainRandomLaw I) (((mainRandomLaw I).map (mainSketchFiniteSample I)).prod (mainCoreLawOriginal I)) :=
  ⟨(mainSketchFiniteSample_measurable I).prodMk (mainCoreTapeOriginal_measurable I),
    mainSketchFiniteSample_coreTape_map I⟩

end
end HierarchicalAbsoluteSpectral
