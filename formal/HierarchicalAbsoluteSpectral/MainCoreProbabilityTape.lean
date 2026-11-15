import HierarchicalAbsoluteSpectral.MainCoreExtensionality
import HierarchicalAbsoluteSpectral.GaussianLeadingRestriction

/-! Restriction of the original, independent core tape to the computed
support dimension, and regrouping by the history available at each stage. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
variable {n m p r L k : ℕ}

abbrev MainCoreQueryTape (I : FixedProblem n m p r L) (k : ℕ) :=
  Fin I.queryCap → Fin I.repetitions → Fin (r+1) → Fin k → ℝ

abbrev MainCoreInertiaTape (I : FixedProblem n m p r L) (k : ℕ) :=
  Fin I.queryCap → Fin I.repetitions → Fin 2 → Fin (k*k) → ℝ

abbrev MainCoreTapeSized (I : FixedProblem n m p r L) (k : ℕ) :=
  (Fin r → Fin k → ℝ) × (MainCoreQueryTape I k ×
    (MainCoreInertiaTape I k × (Fin r → Fin k → ℝ)))

def mainCoreQueryLaw (I : FixedProblem n m p r L) (k : ℕ) : Measure (MainCoreQueryTape I k) :=
  Measure.pi (fun _ : Fin I.queryCap => repeatedGaussianColumns k (r+1) I.repetitions)

def mainCoreInertiaLaw (I : FixedProblem n m p r L) (k : ℕ) : Measure (MainCoreInertiaTape I k) :=
  Measure.pi (fun _ : Fin I.queryCap => Measure.pi (fun _ : Fin I.repetitions =>
    Measure.pi (fun _ : Fin 2 => gaussianVector (k*k))))

def mainCoreLawSized (I : FixedProblem n m p r L) (k : ℕ) : Measure (MainCoreTapeSized I k) :=
  (gaussianColumns k r).prod ((mainCoreQueryLaw I k).prod
    ((mainCoreInertiaLaw I k).prod (gaussianColumns k r)))

instance mainCoreQueryLaw_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreQueryLaw I k) := by
  unfold mainCoreQueryLaw
  infer_instance

instance mainCoreInertiaLaw_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreInertiaLaw I k) := by
  unfold mainCoreInertiaLaw
  infer_instance

instance mainCoreLawSized_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreLawSized I k) := by
  unfold mainCoreLawSized
  infer_instance

def mainCoreTapeRestrict (I : FixedProblem n m p r L) (hkm : k ≤ m)
    (c : MainCoreTapeOriginal I) : MainCoreTapeSized I k :=
  ⟨(fun j i => c.1 j (Fin.castLE hkm i)),
    (fun q u j i => c.2.1 q u j (Fin.castLE hkm i)),
    (fun q u t i => c.2.2.1 q u t (Fin.castLE (Nat.mul_le_mul hkm hkm) i)),
    (fun j i => c.2.2.2 j (Fin.castLE hkm i))⟩

theorem gaussianColumns_rows_measurePreserving (a b w : ℕ) (hba : b ≤ a) :
    MeasurePreserving (fun G : Fin w → Fin a → ℝ => fun j i => G j (Fin.castLE hba i))
      (gaussianColumns a w) (gaussianColumns b w) :=
  measurePreserving_pi (fun _ : Fin w => gaussianVector a)
    (fun _ : Fin w => gaussianVector b)
    (fun _ => gaussianVector_restrict_measurePreserving a b (Fin.castLEEmb hba))

theorem mainCoreTapeRestrict_measurePreserving (I : FixedProblem n m p r L) (hkm : k ≤ m) :
    MeasurePreserving (mainCoreTapeRestrict I hkm) (mainCoreLawOriginal I) (mainCoreLawSized I k) := by
  have hinit := gaussianColumns_rows_measurePreserving m k r hkm
  have htrial := gaussianColumns_rows_measurePreserving m k (r+1) hkm
  have hquery := measurePreserving_pi
    (fun _ : Fin I.queryCap => repeatedGaussianColumns m (r+1) I.repetitions)
    (fun _ : Fin I.queryCap => repeatedGaussianColumns k (r+1) I.repetitions)
    (fun _ => measurePreserving_pi (fun _ : Fin I.repetitions => gaussianColumns m (r+1))
      (fun _ : Fin I.repetitions => gaussianColumns k (r+1)) (fun _ => htrial))
  have hvec := gaussianVector_restrict_measurePreserving (m*m) (k*k)
    (Fin.castLEEmb (Nat.mul_le_mul hkm hkm))
  have hinertia := measurePreserving_pi
    (fun _ : Fin I.queryCap => Measure.pi (fun _ : Fin I.repetitions =>
      Measure.pi (fun _ : Fin 2 => gaussianVector (m*m))))
    (fun _ : Fin I.queryCap => Measure.pi (fun _ : Fin I.repetitions =>
      Measure.pi (fun _ : Fin 2 => gaussianVector (k*k))))
    (fun _ => measurePreserving_pi
      (fun _ : Fin I.repetitions => Measure.pi (fun _ : Fin 2 => gaussianVector (m*m)))
      (fun _ : Fin I.repetitions => Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)))
      (fun _ => measurePreserving_pi (fun _ : Fin 2 => gaussianVector (m*m))
        (fun _ : Fin 2 => gaussianVector (k*k)) (fun _ => hvec)))
  exact hinit.prod (hquery.prod (hinertia.prod hinit))

abbrev MainCoreInitialHistory (I : FixedProblem n m p r L) (k : ℕ) :=
  (Fin r → Fin k → ℝ) × MainCoreQueryTape I k

abbrev MainCoreHistory (I : FixedProblem n m p r L) (k : ℕ) :=
  MainCoreInitialHistory I k × MainCoreInertiaTape I k

abbrev MainCoreTapeGrouped (I : FixedProblem n m p r L) (k : ℕ) :=
  MainCoreHistory I k × (Fin r → Fin k → ℝ)

def mainCoreInitialHistoryLaw (I : FixedProblem n m p r L) (k : ℕ) :
    Measure (MainCoreInitialHistory I k) :=
  (gaussianColumns k r).prod (mainCoreQueryLaw I k)

def mainCoreHistoryLaw (I : FixedProblem n m p r L) (k : ℕ) : Measure (MainCoreHistory I k) :=
  (mainCoreInitialHistoryLaw I k).prod (mainCoreInertiaLaw I k)

def mainCoreLawGrouped (I : FixedProblem n m p r L) (k : ℕ) : Measure (MainCoreTapeGrouped I k) :=
  (mainCoreHistoryLaw I k).prod (gaussianColumns k r)

instance mainCoreInitialHistoryLaw_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreInitialHistoryLaw I k) := by
  unfold mainCoreInitialHistoryLaw
  infer_instance

instance mainCoreHistoryLaw_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreHistoryLaw I k) := by
  unfold mainCoreHistoryLaw
  infer_instance

instance mainCoreLawGrouped_isProbability (I : FixedProblem n m p r L) (k : ℕ) :
    IsProbabilityMeasure (mainCoreLawGrouped I k) := by
  unfold mainCoreLawGrouped
  infer_instance

def mainCoreRegroup (I : FixedProblem n m p r L) (c : MainCoreTapeSized I k) :
    MainCoreTapeGrouped I k := (((c.1,c.2.1),c.2.2.1),c.2.2.2)

theorem mainCoreRegroup_measurePreserving (I : FixedProblem n m p r L) (k : ℕ) :
    MeasurePreserving (mainCoreRegroup I) (mainCoreLawSized I k) (mainCoreLawGrouped I k) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (gaussianColumns k r) (mainCoreQueryLaw I k)
      ((mainCoreInertiaLaw I k).prod (gaussianColumns k r)))
  have h₂ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ((gaussianColumns k r).prod (mainCoreQueryLaw I k))
      (mainCoreInertiaLaw I k) (gaussianColumns k r))
  exact h₂.comp h₁

def mainCoreOriginalToGrouped (I : FixedProblem n m p r L) (hkm : k ≤ m) :
    MainCoreTapeOriginal I → MainCoreTapeGrouped I k :=
  fun c => mainCoreRegroup I (mainCoreTapeRestrict I hkm c)

theorem mainCoreOriginalToGrouped_measurePreserving (I : FixedProblem n m p r L) (hkm : k ≤ m) :
    MeasurePreserving (mainCoreOriginalToGrouped I hkm) (mainCoreLawOriginal I) (mainCoreLawGrouped I k) :=
  (mainCoreRegroup_measurePreserving I k).comp (mainCoreTapeRestrict_measurePreserving I hkm)

theorem mainCoreProgramFromOriginalTape_eq_restrict
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (c : MainCoreTapeOriginal I) :
    mainCoreProgramFromOriginalTape kernels I S C c =
      let g := mainCoreOriginalToGrouped I (mainSupport_dimension_le S C) c
      mainCoreProgramFromArrays kernels I S C g.1.1.1 g.1.1.2 g.1.2 g.2 := rfl

end
end HierarchicalAbsoluteSpectral
