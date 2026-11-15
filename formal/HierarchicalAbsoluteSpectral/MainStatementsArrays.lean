import HierarchicalAbsoluteSpectral.MainStatementsCore
import HierarchicalAbsoluteSpectral.MainStatementsTapeLaw

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
variable {n m p r L : ℕ}

theorem mainSupport_dimension_le (S : StoredSketches n m p L) (C : MainSupportData S) :
    C.pair.dimension ≤ m := by simpa only [Fintype.card_fin] using C.pair.dimension_le

def mainInitializerArray (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) : Fin r → Fin C.pair.dimension → ℝ :=
  fun j i => g (.initializer j (Fin.castLE (mainSupport_dimension_le S C) i))

def mainQueryArray (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) (number : Fin I.queryCap) :
    Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ :=
  fun trial j i => g (.query number trial j (Fin.castLE (mainSupport_dimension_le S C) i))

def mainInertiaArray (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) (number : Fin I.queryCap) :
    Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ :=
  fun trial test i => g (.inertia number trial test
    (Fin.castLE (Nat.mul_le_mul (mainSupport_dimension_le S C) (mainSupport_dimension_le S C)) i))

def mainStrongArray (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (g : MainRandomTape I) : Fin r → Fin C.pair.dimension → ℝ :=
  fun j i => g (.strong j (Fin.castLE (mainSupport_dimension_le S C) i))

def mainInitializerEmbedding (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) :
    (Fin r × Fin C.pair.dimension) ↪ MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .initializer x.1 (Fin.castLE (mainSupport_dimension_le S C) x.2)
  inj' := by
    intro x y hxy
    have hh := MainGaussianIndex.initializer.inj hxy
    exact Prod.ext hh.1 (Fin.ext (congrArg (fun z : Fin m => z.val) hh.2))

theorem mainInitializerArray_measurePreserving (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    MeasurePreserving (mainInitializerArray I S C) (mainRandomLaw I)
      (gaussianColumns C.pair.dimension r) :=
  gaussianTape_blocks_measurePreserving r C.pair.dimension (mainInitializerEmbedding I S C)

def mainStrongEmbedding (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) :
    (Fin r × Fin C.pair.dimension) ↪ MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .strong x.1 (Fin.castLE (mainSupport_dimension_le S C) x.2)
  inj' := by
    intro x y hxy
    have hh := MainGaussianIndex.strong.inj hxy
    exact Prod.ext hh.1 (Fin.ext (congrArg (fun z : Fin m => z.val) hh.2))

theorem mainStrongArray_measurePreserving (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    MeasurePreserving (mainStrongArray I S C) (mainRandomLaw I)
      (gaussianColumns C.pair.dimension r) :=
  gaussianTape_blocks_measurePreserving r C.pair.dimension (mainStrongEmbedding I S C)

def mainQueriesEmbedding (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) :
    (Fin I.queryCap × (Fin I.repetitions × (Fin (r+1) × Fin C.pair.dimension))) ↪
      MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .query x.1 x.2.1 x.2.2.1 (Fin.castLE (mainSupport_dimension_le S C) x.2.2.2)
  inj' := by
    intro x y hxy
    have hh := MainGaussianIndex.query.inj hxy
    exact Prod.ext hh.1 (Prod.ext hh.2.1 (Prod.ext hh.2.2.1
      (Fin.ext (congrArg (fun z : Fin m => z.val) hh.2.2.2))))

theorem mainQueryArray_measurePreserving (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    MeasurePreserving (fun g => mainQueryArray I S C g) (mainRandomLaw I)
      (Measure.pi (fun _ : Fin I.queryCap => repeatedGaussianColumns C.pair.dimension (r+1) I.repetitions)) :=
  gaussianTape_array4_measurePreserving (mainQueriesEmbedding I S C)

def mainInertiasEmbedding (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) :
    (Fin I.queryCap × (Fin I.repetitions × (Fin 2 × Fin (C.pair.dimension*C.pair.dimension)))) ↪
      MainGaussianIndex n m p r L I.queryCap I.repetitions where
  toFun x := .inertia x.1 x.2.1 x.2.2.1
    (Fin.castLE (Nat.mul_le_mul (mainSupport_dimension_le S C) (mainSupport_dimension_le S C)) x.2.2.2)
  inj' := by
    intro x y hxy
    have hh := MainGaussianIndex.inertia.inj hxy
    exact Prod.ext hh.1 (Prod.ext hh.2.1 (Prod.ext hh.2.2.1
      (Fin.ext (congrArg (fun z : Fin (m*m) => z.val) hh.2.2.2))))

theorem mainInertiaArray_measurePreserving (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    MeasurePreserving (fun g => mainInertiaArray I S C g) (mainRandomLaw I)
      (Measure.pi (fun _ : Fin I.queryCap => Measure.pi (fun _ : Fin I.repetitions =>
        Measure.pi (fun _ : Fin 2 => gaussianVector (C.pair.dimension*C.pair.dimension))))) :=
  gaussianTape_array4_measurePreserving (mainInertiasEmbedding I S C)


end
end HierarchicalAbsoluteSpectral
