import HierarchicalAbsoluteSpectral.MainScalarProgram

/-! Matrix actions consume the scalar values returned by `mainScalarProgram`.
The subtype certificates only identify their matrix targets. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

@[simp] theorem safeAccuracy_at_safeSketchIndex (I : FixedProblem n m p r L) (j : ℕ) :
    safeAccuracy I (safeSketchIndex L j).val = safeAccuracy I j := by
  simp only [safeAccuracy, safeSketchIndex, min_assoc, min_self]

def FactorActions.castMatrix {k b : ℕ} {R T : Core k}
    (A : FactorActions R b) (h : R = T) : FactorActions T b where
  forward := A.forward.castMatrix h
  transpose := A.transpose.castMatrix (congrArg Matrix.transpose h)

theorem MatrixAction.castMatrix_congr {a c b : ℕ} {α : Type}
    {A : α → Matrix (Fin a) (Fin c) ℝ}
    (F : ∀ x, MatrixAction (A x) b) {x y : α} (h : x = y)
    {B : Matrix (Fin a) (Fin c) ℝ} (hx : A x = B) (hy : A y = B) :
    (F x).castMatrix hx = (F y).castMatrix hy := by
  subst y
  rfl

def mainPreparedFinePencilAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (j b : ℕ) : MatrixAction (mainFinePencil I S C t j) b :=
  (storedFinePencilAction kernels (S.levelA (safeSketchIndex L (j+1))).2
    (S.levelB (safeSketchIndex L (j+1))).2 C.pair.factor C.pair.leftInverseᵀ t
    (P.fineMass.val (safeSketchIndex L (j+1))) (by
      rw [P.fineMass.property]
      simp only [safeAccuracy_at_safeSketchIndex]
      exact div_pos (safeAccuracy_pos I (j+1)) (by norm_num))).castMatrix (by
      simp only [trueNeumannPencil, mainFinePencil, fineNeumannPencil, mainFineGram,
        mainFineRightGram, StoredSketches.leftGram, StoredSketches.rightGram,
        Matrix.transpose_transpose]
      congr 3
      rw [P.fineMass.property]
      simp only [safeAccuracy_at_safeSketchIndex])

theorem mainPreparedFinePencilAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (j b : ℕ) :
    mainPreparedFinePencilAction kernels I P S C t j b =
      mainFinePencilAction kernels I S C t j b := by
  rw [PreparedMainScalars.eq_canonical I P]
  unfold mainPreparedFinePencilAction mainFinePencilAction
  let x : {ε : ℝ // 0 < ε} :=
    ⟨safeAccuracy I (safeSketchIndex L (j+1)).val/100,
      div_pos (safeAccuracy_pos I _) (by norm_num)⟩
  let y : {ε : ℝ // 0 < ε} :=
    ⟨safeAccuracy I (j+1)/100, div_pos (safeAccuracy_pos I _) (by norm_num)⟩
  have hxy : x = y := Subtype.ext (by simp only [x, y, safeAccuracy_at_safeSketchIndex])
  apply MatrixAction.castMatrix_congr
    (A := fun ε : {ε : ℝ // 0 < ε} =>
      trueNeumannPencil
        (C.pair.leftInverseᵀᵀ *
          ((S.levelA (safeSketchIndex L (j+1))).2ᵀ * (S.levelA (safeSketchIndex L (j+1))).2) *
          C.pair.leftInverseᵀ)
        (C.pair.factorᵀ *
          ((S.levelB (safeSketchIndex L (j+1))).2ᵀ * (S.levelB (safeSketchIndex L (j+1))).2) *
          C.pair.factor)
        t ε.val ε.property)
    (fun ε : {ε : ℝ // 0 < ε} =>
      storedFinePencilAction kernels (S.levelA (safeSketchIndex L (j+1))).2
        (S.levelB (safeSketchIndex L (j+1))).2 C.pair.factor C.pair.leftInverseᵀ t
        ε.val ε.property) hxy

@[simp] theorem mainPreparedFinePencilAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (j b : ℕ) :
    (mainPreparedFinePencilAction kernels I P S C t j b).program =
      (mainFinePencilAction kernels I S C t j b).program := by
  rw [mainPreparedFinePencilAction_eq]

@[simp] theorem mainPreparedFinePencilAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (j b : ℕ) :
    (mainPreparedFinePencilAction kernels I P S C t j b).cost =
      (mainFinePencilAction kernels I S C t j b).cost := by
  rw [mainPreparedFinePencilAction_eq]

def mainPreparedTruePencilAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (b : ℕ) :
    MatrixAction (mainTruePencil I S C t) b :=
  (storedFinePencilAction kernels I.A I.Bᵀ C.pair.factor C.pair.leftInverseᵀ t
    P.mass.val (by rw [P.mass.property]; exact I.final_budget.mass_positive)).castMatrix (by
      simp only [trueNeumannPencil, mainTruePencil, mainTrueGram, mainTrueRightGram,
        Matrix.transpose_transpose]
      congr 3
      exact P.mass.property)

theorem mainPreparedTruePencilAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (b : ℕ) :
    mainPreparedTruePencilAction kernels I P S C t b = mainTruePencilAction kernels I S C t b := by
  rw [PreparedMainScalars.eq_canonical I P]
  rfl

@[simp] theorem mainPreparedTruePencilAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (b : ℕ) :
    (mainPreparedTruePencilAction kernels I P S C t b).program =
      (mainTruePencilAction kernels I S C t b).program := by
  rw [mainPreparedTruePencilAction_eq]

@[simp] theorem mainPreparedTruePencilAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) (b : ℕ) :
    (mainPreparedTruePencilAction kernels I P S C t b).cost =
      (mainTruePencilAction kernels I S C t b).cost := by
  rw [mainPreparedTruePencilAction_eq]

def mainPreparedFactorActionsUpTo (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (j : ℕ) → j ≤ L →
      FactorActions (hierarchicalInverseFactor base.inverseFactor
        (mainFinePencil I S C t) (safeAccuracy I) j) b
  | 0, _ =>
      { forward := (kernels _ _ b).action base.inverseFactor
        transpose := (kernels _ _ b).action base.inverseFactorᵀ }
  | j+1, hj =>
      ((mainPreparedFactorActionsUpTo kernels I P S C t base b j (by omega)).refine
        (mainPreparedFinePencilAction kernels I P S C t j b)
        (mainFinePencil_transpose I S C t j)
        (P.ratios.val ⟨j, by omega⟩) (safeAccuracy I (j+1)) (hierarchyUpper j)
        (by rw [P.ratios.property]; exact div_pos (safeAccuracy_pos I (j+1)) (safeAccuracy_pos I j))
        (safeAccuracy_pos I (j+1)) (hierarchyUpper_nonneg j)).castMatrix (by
          rw [P.ratios.property]
          rfl)

theorem mainPreparedFactorActionsUpTo_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b j : ℕ) (hj : j ≤ L) :
    mainPreparedFactorActionsUpTo kernels I P S C t base b j hj =
      hierarchicalFactorActions base.inverseFactor (mainFinePencil I S C t) (safeAccuracy I) L
        (fun j _ => safeAccuracy_pos I j) (fun j _ => mainFinePencil_transpose I S C t j)
        { forward := (kernels _ _ b).action base.inverseFactor
          transpose := (kernels _ _ b).action base.inverseFactorᵀ }
        (fun j => mainFinePencilAction kernels I S C t j b) j hj := by
  rw [PreparedMainScalars.eq_canonical I P]
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [mainPreparedFactorActionsUpTo, hierarchicalFactorActions]
      rw [ih, mainPreparedFinePencilAction_eq]
      rfl

def mainPreparedFactorActions (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    FactorActions (mainRefinedFactor I S C t base) b :=
  mainPreparedFactorActionsUpTo kernels I P S C t base b L le_rfl

theorem mainPreparedFactorActions_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    mainPreparedFactorActions kernels I P S C t base b = mainFactorActions kernels I S C t base b :=
  mainPreparedFactorActionsUpTo_eq kernels I P S C t base b L le_rfl

@[simp] theorem mainPreparedFactorActions_forward_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedFactorActions kernels I P S C t base b).forward.program =
      (mainFactorActions kernels I S C t base b).forward.program := by
  rw [mainPreparedFactorActions_eq]

@[simp] theorem mainPreparedFactorActions_transpose_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedFactorActions kernels I P S C t base b).transpose.program =
      (mainFactorActions kernels I S C t base b).transpose.program := by
  rw [mainPreparedFactorActions_eq]

@[simp] theorem mainPreparedFactorActions_forward_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedFactorActions kernels I P S C t base b).forward.cost =
      (mainFactorActions kernels I S C t base b).forward.cost := by
  rw [mainPreparedFactorActions_eq]

@[simp] theorem mainPreparedFactorActions_transpose_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedFactorActions kernels I P S C t base b).transpose.cost =
      (mainFactorActions kernels I S C t base b).transpose.cost := by
  rw [mainPreparedFactorActions_eq]

def mainPreparedThresholdAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (mainThresholdOperator I S C t base) b :=
  (MatrixAction.identity _ b).sub
    (normalizedMatrixAction (mainPreparedFactorActions kernels I P S C t base b).forward
      (mainPreparedFactorActions kernels I P S C t base b).transpose
      (mainPreparedTruePencilAction kernels I P S C t b))

theorem mainPreparedThresholdAction_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    mainPreparedThresholdAction kernels I P S C t base b =
      mainThresholdAction kernels I S C t base b := by
  simp only [mainPreparedThresholdAction, mainThresholdAction,
    mainPreparedFactorActions_eq, mainPreparedTruePencilAction_eq]

@[simp] theorem mainPreparedThresholdAction_program
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedThresholdAction kernels I P S C t base b).program =
      (mainThresholdAction kernels I S C t base b).program := by
  rw [mainPreparedThresholdAction_eq]

@[simp] theorem mainPreparedThresholdAction_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (P : PreparedMainScalars I)
    (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    (mainPreparedThresholdAction kernels I P S C t base b).cost =
      (mainThresholdAction kernels I S C t base b).cost := by
  rw [mainPreparedThresholdAction_eq]

end
end HierarchicalAbsoluteSpectral
