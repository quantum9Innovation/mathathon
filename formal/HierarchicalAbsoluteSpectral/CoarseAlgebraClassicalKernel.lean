import HierarchicalAbsoluteSpectral.ArithmeticKernel

/-! Conventional dot-product matrix circuits, with exactly 2*n*m*p
executed field operations. They supply the wide-block fallback. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.UniversalProgram
open scoped BigOperators

def finiteCircuitSum {I : Type} : (n : ℕ) → (Fin n → Circuit I PUnit) → Circuit I PUnit
  | 0, _ => .zero
  | n+1, f => Circuit.sum (f 0) (finiteCircuitSum n (fun i => f i.succ))

theorem finiteCircuitSum_eval {I : Type} (n : ℕ) (f : Fin n → Circuit I PUnit)
    (input : I → ℝ) :
    (finiteCircuitSum n f).eval input PUnit.unit = ∑ i, (f i).eval input PUnit.unit := by
  induction n with
  | zero => simp [finiteCircuitSum]
  | succ n ih => simp [finiteCircuitSum, ih, Fin.sum_univ_succ]

theorem finiteCircuitSum_cost {I : Type} (n : ℕ) (f : Fin n → Circuit I PUnit) :
    (finiteCircuitSum n f).cost = (∑ i, (f i).cost)+n := by
  induction n with
  | zero => simp [finiteCircuitSum]
  | succ n ih => simp only [finiteCircuitSum, Circuit.sum_cost, ih, Fin.sum_univ_succ]; omega

def classicalEntryCircuit (n m p : ℕ) (i : Fin n) (j : Fin p) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p)) PUnit :=
  finiteCircuitSum m (fun k => .comp (.wire (fun b : Bool =>
    if b then Sum.inr (k,j) else Sum.inl (i,k))) .mul)

def classicalArithmeticKernels (n m p : ℕ) : ArithmeticKernel n m p where
  circuit := .comp (.bundle (fun q : Fin n × Fin p => classicalEntryCircuit n m p q.1 q.2))
    (.wire (fun q => (q,PUnit.unit)))
  correct A B i j := by
    simp only [Circuit.eval_comp, Circuit.eval_bundle, Circuit.eval_wire]
    rw [classicalEntryCircuit, finiteCircuitSum_eval]
    simp [matrixCircuitInput, Matrix.mul_apply]

@[simp] theorem classicalArithmeticKernels_cost (n m p : ℕ) :
    (classicalArithmeticKernels n m p).cost = 2*n*m*p := by
  simp only [ArithmeticKernel.cost, classicalArithmeticKernels, Circuit.comp_cost,
    Circuit.bundle_cost, Circuit.wire_cost, add_zero, classicalEntryCircuit,
    finiteCircuitSum_cost, Circuit.mul_cost]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Fintype.card_prod]
  ring

end
end HierarchicalAbsoluteSpectral
