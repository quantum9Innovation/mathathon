import HierarchicalAbsoluteSpectral.MainSketchFiniteState
import HierarchicalAbsoluteSpectral.MainStatementsTapeLaw
import HierarchicalAbsoluteSpectral.ThresholdRepetitions

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory
variable {n m p r L : ℕ}

abbrev MainSketchRawIndex (n p L : ℕ) :=
  (Fin (L+1) × (Fin 3 × Fin (2^dyadicPaddingLevel n))) ⊕
  (Fin (L+1) × (Fin 3 × Fin (2^dyadicPaddingLevel p)))

abbrev MainInitializerRawIndex (m r : ℕ) := Fin r × Fin m
abbrev MainQueryRawIndex (m r cap rep : ℕ) := Fin cap × (Fin rep × (Fin (r+1) × Fin m))
abbrev MainInertiaRawIndex (m cap rep : ℕ) := Fin cap × (Fin rep × (Fin 2 × Fin (m*m)))
abbrev MainCoreRawIndex (m r cap rep : ℕ) := MainInitializerRawIndex m r ⊕
  (MainQueryRawIndex m r cap rep ⊕ (MainInertiaRawIndex m cap rep ⊕ MainInitializerRawIndex m r))

abbrev MainCoreTapeOriginal (I : FixedProblem n m p r L) :=
  (Fin r → Fin m → ℝ) × ((Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin m → ℝ) ×
    ((Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (m*m) → ℝ) × (Fin r → Fin m → ℝ)))

def mainCoreTapeOriginal (I : FixedProblem n m p r L) (g : MainRandomTape I) : MainCoreTapeOriginal I :=
  ((fun j i => g (.initializer j i)),((fun q u j i => g (.query q u j i)),
    ((fun q u t i => g (.inertia q u t i)),(fun j i => g (.strong j i)))))

def mainCoreLawOriginal (I : FixedProblem n m p r L) : Measure (MainCoreTapeOriginal I) :=
  (gaussianColumns m r).prod ((Measure.pi (fun _ : Fin I.queryCap =>
    repeatedGaussianColumns m (r+1) I.repetitions)).prod
      ((Measure.pi (fun _ : Fin I.queryCap => Measure.pi (fun _ : Fin I.repetitions =>
        Measure.pi (fun _ : Fin 2 => gaussianVector (m*m))))).prod (gaussianColumns m r)))

instance mainCoreLawOriginal_isProbability (I : FixedProblem n m p r L) :
    IsProbabilityMeasure (mainCoreLawOriginal I) := by
  unfold mainCoreLawOriginal
  infer_instance

def mainTapePartition (I : FixedProblem n m p r L) :
    (MainSketchRawIndex n p L ⊕ MainCoreRawIndex m r I.queryCap I.repetitions) ≃
      MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun
    | .inl (.inl (j,(b,i))) => .sketchLeft j b i
    | .inl (.inr (j,(b,i))) => .sketchRight j b i
    | .inr (.inl (j,i)) => .initializer j i
    | .inr (.inr (.inl (q,(u,(j,i))))) => .query q u j i
    | .inr (.inr (.inr (.inl (q,(u,(t,i)))))) => .inertia q u t i
    | .inr (.inr (.inr (.inr (j,i)))) => .strong j i
  invFun
    | .sketchLeft j b i => .inl (.inl (j,(b,i)))
    | .sketchRight j b i => .inl (.inr (j,(b,i)))
    | .initializer j i => .inr (.inl (j,i))
    | .query q u j i => .inr (.inr (.inl (q,(u,(j,i)))))
    | .inertia q u t i => .inr (.inr (.inr (.inl (q,(u,(t,i))))))
    | .strong j i => .inr (.inr (.inr (.inr (j,i))))
  left_inv := by
    intro x
    rcases x with ((⟨j,b,i⟩ | ⟨j,b,i⟩) | (⟨j,i⟩ | (⟨q,u,j,i⟩ | (⟨q,u,t,i⟩ | ⟨j,i⟩)))) <;> rfl
  right_inv := by intro x; cases x <;> rfl

def mainSketchRawSample (I : FixedProblem n m p r L) (s : MainSketchRawIndex n p L → ℝ) :
    MainSketchSampleTape I :=
  ((fun j => gaussianSRHTSample (dyadicPaddingLevel n)
      (embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure)
      (min_le_left _ _) ((fun i => s (.inl (j,(0,i)))),
        ((fun i => s (.inl (j,(1,i)))),(fun i => s (.inl (j,(2,i))))))),
    (fun j => gaussianSRHTSample (dyadicPaddingLevel p)
      (embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure)
      (min_le_left _ _) ((fun i => s (.inr (j,(0,i)))),
        ((fun i => s (.inr (j,(1,i)))),(fun i => s (.inr (j,(2,i))))))))

theorem mainSketchRawSample_measurable (I : FixedProblem n m p r L) :
    Measurable (mainSketchRawSample I) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro j
    apply (gaussianSRHTSample_measurable _ _ _).comp
    fun_prop
  · apply measurable_pi_lambda
    intro j
    apply (gaussianSRHTSample_measurable _ _ _).comp
    fun_prop

def mainCoreRawCurry (I : FixedProblem n m p r L)
    (c : MainCoreRawIndex m r I.queryCap I.repetitions → ℝ) : MainCoreTapeOriginal I :=
  ⟨(fun j i => c (.inl (j,i))), (fun q u j i => c (.inr (.inl (q,(u,(j,i)))))),
    (fun q u t i => c (.inr (.inr (.inl (q,(u,(t,i))))))),
    (fun j i => c (.inr (.inr (.inr (j,i)))))⟩

theorem gaussianSum_measurePreserving {A B : Type*} [Fintype A] [Fintype B] :
    MeasurePreserving (fun g : A ⊕ B → ℝ => ((fun a => g (.inl a)),(fun b => g (.inr b))))
      (Measure.pi (fun _ : A ⊕ B => gaussianReal 0 1))
      ((Measure.pi (fun _ : A => gaussianReal 0 1)).prod (Measure.pi (fun _ : B => gaussianReal 0 1))) :=
  measurePreserving_sumPiEquivProdPi (fun _ => gaussianReal 0 1)

end
end HierarchicalAbsoluteSpectral
