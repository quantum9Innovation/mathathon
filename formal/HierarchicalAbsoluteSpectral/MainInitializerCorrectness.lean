import HierarchicalAbsoluteSpectral.MainInitializerCorrectnessBase
import HierarchicalAbsoluteSpectral.MainStatementsAlgorithm

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem MainSketchGood.mainCoreProgram_exact_of_small_dimension
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (g : MainRandomTape I) (hr : C.pair.dimension ≤ r) :
    (mainCoreProgram kernels I S C g).eval.product = I.A*I.B := by
  rw [mainCoreProgram, dif_pos hr]
  exact supportExactOutputProgram_exact kernels I.A I.B
    (supportLeftFactor I.A S.initialA C.pair) (supportRightFactor S.initialA C.pair I.B)
    (hg.support_exact I S C) _ hr

theorem MainSketchGood.mainCoreProgram_exact_of_initializer_exact
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (g : MainRandomTape I)
    (hexact : (gaussianInitializerProgram kernels C.rightGram
      (columnsMatrix (mainInitializerArray I S C g)) I.singleFailure).eval.result = .exact) :
    (mainCoreProgram kernels I S C g).eval.product = I.A*I.B := by
  by_cases hr : C.pair.dimension ≤ r
  · exact hg.mainCoreProgram_exact_of_small_dimension kernels I S C g hr
  · simp only [mainCoreProgram, dif_neg hr, ArithmeticProgram.eval_bind, hexact]
    exact hg.initializer_exact_physical_output kernels I S C _ hexact

end
end HierarchicalAbsoluteSpectral
