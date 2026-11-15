import HierarchicalAbsoluteSpectral.MainSketchData
import HierarchicalAbsoluteSpectral.SupportProgram
import HierarchicalAbsoluteSpectral.CompiledHierarchy
import HierarchicalAbsoluteSpectral.BaseStoredActions

/-! Compositional operator constructor from the stored sketches and the
executed coarse base. Large support matrices and fine factors remain operators. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def StoredSketches.initialA (S : StoredSketches n m p L) := (S.levelA 0).2
def StoredSketches.initialB (S : StoredSketches n m p L) := (S.levelB 0).2
abbrev MainSupportData (S : StoredSketches n m p L) :=
  CoarseSupportData S.initialA S.initialB

def safeAccuracy (I : FixedProblem n m p r L) (j : ℕ) : ℝ := I.accuracy (min j L)
theorem safeAccuracy_pos (I : FixedProblem n m p r L) (j : ℕ) : 0<safeAccuracy I j :=
  I.accuracy_positive _ (min_le_right _ _)

def safeSketchIndex (L j : ℕ) : Fin (L+1) := ⟨min j L,by omega⟩

def mainTrueGram (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : Core C.pair.dimension :=
  C.pair.leftInverse*(I.Aᵀ*I.A)*C.pair.leftInverseᵀ

def mainTrueRightGram (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : Core C.pair.dimension := C.pair.factorᵀ*(I.B*I.Bᵀ)*C.pair.factor

def mainFineGram (S : StoredSketches n m p L) (C : MainSupportData S) (j : ℕ) : Core C.pair.dimension :=
  C.pair.leftInverse*S.leftGram (safeSketchIndex L j)*C.pair.leftInverseᵀ

def mainFineRightGram (S : StoredSketches n m p L) (C : MainSupportData S) (j : ℕ) : Core C.pair.dimension :=
  C.pair.factorᵀ*S.rightGram (safeSketchIndex L j)*C.pair.factor

def mainTruePencil (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) : Core C.pair.dimension :=
  trueNeumannPencil (mainTrueGram I S C) (mainTrueRightGram I S C) t I.massAccuracy I.final_budget.mass_positive

def mainFinePencil (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (j : ℕ) : Core C.pair.dimension :=
  fineNeumannPencil (mainFineGram S C (j+1)) (mainFineRightGram S C (j+1))
    t (safeAccuracy I (j+1)) (safeAccuracy_pos I (j+1))

theorem mainFinePencil_transpose (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (j : ℕ) : (mainFinePencil I S C t j)ᵀ=mainFinePencil I S C t j := by
  have hG : (mainFineGram S C (j+1)).IsHermitian := by
    simpa only [mainFineGram, StoredSketches.leftGram,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc] using
      (Matrix.posSemidef_conjTranspose_mul_self ((S.levelA (safeSketchIndex L (j+1))).2*C.pair.leftInverseᵀ)).isHermitian
  have hm := (constructedNeumannMass_posDef _ hG (safeAccuracy I (j+1)/100) (by
    have := safeAccuracy_pos I (j+1); positivity)).isHermitian.eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hm
  simp [mainFinePencil,fineNeumannPencil,hm,mainFineRightGram,StoredSketches.rightGram,
    Matrix.transpose_mul,Matrix.mul_assoc]

def mainFinePencilAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (j b : ℕ) : MatrixAction (mainFinePencil I S C t j) b :=
  (storedFinePencilAction kernels (S.levelA (safeSketchIndex L (j+1))).2
    (S.levelB (safeSketchIndex L (j+1))).2 C.pair.factor C.pair.leftInverseᵀ t
    (safeAccuracy I (j+1)/100) (by have := safeAccuracy_pos I (j+1); positivity)).castMatrix (by
      simp only [trueNeumannPencil,mainFinePencil,fineNeumannPencil,mainFineGram,
        mainFineRightGram,StoredSketches.leftGram,StoredSketches.rightGram,Matrix.transpose_transpose])

def mainTruePencilAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (b : ℕ) : MatrixAction (mainTruePencil I S C t) b :=
  (storedFinePencilAction kernels I.A I.Bᵀ C.pair.factor C.pair.leftInverseᵀ t
    I.massAccuracy I.final_budget.mass_positive).castMatrix (by
      simp only [mainTruePencil,mainTrueGram,mainTrueRightGram,Matrix.transpose_transpose])

abbrev MainBaseData (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) :=
  BaseConstruction (t • (1 : Core C.pair.dimension)+C.rightGram)
    (t • (1 : Core C.pair.dimension)-C.rightGram) (I.accuracy 0) (I.accuracy_positive 0 (by omega))

def mainRefinedFactor (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) : Core C.pair.dimension :=
  hierarchicalInverseFactor base.inverseFactor (mainFinePencil I S C t) (safeAccuracy I) L

def mainFactorActions (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) : FactorActions (mainRefinedFactor I S C t base) b :=
  hierarchicalFactorActions base.inverseFactor (mainFinePencil I S C t) (safeAccuracy I) L
    (fun j _ => safeAccuracy_pos I j) (fun j _ => mainFinePencil_transpose I S C t j)
    { forward := (kernels _ _ b).action base.inverseFactor
      transpose := (kernels _ _ b).action base.inverseFactorᵀ }
    (fun j => mainFinePencilAction kernels I S C t j b) L le_rfl

def mainThresholdOperator (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) : Core C.pair.dimension :=
  1-normalizedPencil (mainRefinedFactor I S C t base) (mainTruePencil I S C t)

def mainThresholdAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) : MatrixAction (mainThresholdOperator I S C t base) b :=
  ((MatrixAction.identity _ b).sub
    (normalizedMatrixAction (mainFactorActions kernels I S C t base b).forward
      (mainFactorActions kernels I S C t base b).transpose (mainTruePencilAction kernels I S C t b)))

end
end HierarchicalAbsoluteSpectral
