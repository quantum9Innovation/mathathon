import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedHalfKernel

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix Matmul.UniversalProgram

def columnBlockInputCircuit (n m b q : ℕ) (s : Fin q) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin (q*b)))
      ((Fin n × Fin m) ⊕ (Fin m × Fin b)) :=
  .pair (.wire Sum.inl) (.wire (fun x => Sum.inr (x.1,finProdFinEquiv (s,x.2))))

theorem columnBlockInputCircuit_eval (n m b q : ℕ) (s : Fin q)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin (q*b)) ℝ) :
    (columnBlockInputCircuit n m b q s).eval (matrixCircuitInput A B) =
      matrixCircuitInput A (B.submatrix id (fun j => finProdFinEquiv (s,j))) := by
  funext x
  cases x <;> rfl

def ArithmeticKernel.blockColumns {n m b : ℕ} (K : ArithmeticKernel n m b) (q : ℕ) :
    ArithmeticKernel n m (q*b) where
  circuit := .comp (.bundle (fun s : Fin q =>
    .comp (columnBlockInputCircuit n m b q s) K.circuit))
    (.wire (fun x : Fin n × Fin (q*b) =>
      ((finProdFinEquiv.symm x.2).1,(x.1,(finProdFinEquiv.symm x.2).2))))
  correct A B i j := by
    simp only [Circuit.eval_comp,Circuit.eval_wire,Circuit.eval_bundle,
      columnBlockInputCircuit_eval,K.correct]
    change (A*(B.submatrix id (fun k =>
      finProdFinEquiv ((finProdFinEquiv.symm j).1,k)))) i (finProdFinEquiv.symm j).2 = (A*B) i j
    change (∑ x, A i x*B x (finProdFinEquiv (finProdFinEquiv.symm j))) = (A*B) i j
    rw [Equiv.apply_symm_apply,Matrix.mul_apply]

@[simp] theorem ArithmeticKernel.blockColumns_cost {n m b : ℕ}
    (K : ArithmeticKernel n m b) (q : ℕ) : (K.blockColumns q).cost = q*K.cost := by
  simp [ArithmeticKernel.cost,ArithmeticKernel.blockColumns,columnBlockInputCircuit]

end
end HierarchicalAbsoluteSpectral
