import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedOutputKernelFamily

/-! Tiled inner-half circuits supply the two cyclic row orientations. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Matmul.UniversalProgram Matmul.RectangularPrograms
open scoped BigOperators

def cyclicRowBlockInputCircuit (a b c q : ℕ) (s : Fin q) :
    Circuit ((Fin (q*a) × Fin b) ⊕ (Fin b × Fin c))
      ((Fin a × Fin b) ⊕ (Fin b × Fin c)) :=
  .pair (.wire (fun x => Sum.inl (finProdFinEquiv (s,x.1),x.2))) (.wire Sum.inr)

theorem cyclicRowBlockInputCircuit_eval (a b c q : ℕ) (s : Fin q)
    (A : Matrix (Fin (q*a)) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    (cyclicRowBlockInputCircuit a b c q s).eval (matrixCircuitInput A B) =
      matrixCircuitInput (A.submatrix (fun i => finProdFinEquiv (s,i)) id) B := by
  funext x
  cases x <;> rfl

def ArithmeticKernel.cyclicBlockRows {a b c : ℕ} (K : ArithmeticKernel a b c) (q : ℕ) :
    ArithmeticKernel (q*a) b c where
  circuit := .comp (.bundle (fun s : Fin q =>
    .comp (cyclicRowBlockInputCircuit a b c q s) K.circuit))
    (.wire (fun x : Fin (q*a) × Fin c =>
      ((finProdFinEquiv.symm x.1).1,((finProdFinEquiv.symm x.1).2,x.2))))
  correct A B i j := by
    simp only [Circuit.eval_comp, Circuit.eval_wire, Circuit.eval_bundle,
      cyclicRowBlockInputCircuit_eval, K.correct]
    change ∑ x, A (finProdFinEquiv (finProdFinEquiv.symm i)) x * B x j = (A*B) i j
    rw [Equiv.apply_symm_apply, Matrix.mul_apply]

@[simp] theorem ArithmeticKernel.cyclicBlockRows_cost {a b c : ℕ}
    (K : ArithmeticKernel a b c) (q : ℕ) : (K.cyclicBlockRows q).cost = q*K.cost := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.cyclicBlockRows, cyclicRowBlockInputCircuit]

def cyclicInnerBlockInputCircuit (a b c q : ℕ) (s : Fin q) :
    Circuit ((Fin a × Fin (q*b)) ⊕ (Fin (q*b) × Fin c))
      ((Fin a × Fin b) ⊕ (Fin b × Fin c)) :=
  .pair (.wire (fun x => Sum.inl (x.1,finProdFinEquiv (s,x.2))))
    (.wire (fun x => Sum.inr (finProdFinEquiv (s,x.1),x.2)))

theorem cyclicInnerBlockInputCircuit_eval (a b c q : ℕ) (s : Fin q)
    (A : Matrix (Fin a) (Fin (q*b)) ℝ) (B : Matrix (Fin (q*b)) (Fin c) ℝ) :
    (cyclicInnerBlockInputCircuit a b c q s).eval (matrixCircuitInput A B) =
      matrixCircuitInput (A.submatrix id (fun i => finProdFinEquiv (s,i)))
        (B.submatrix (fun i => finProdFinEquiv (s,i)) id) := by
  funext x
  cases x <;> rfl

def ArithmeticKernel.cyclicBlockInner {a b c : ℕ} (K : ArithmeticKernel a b c) (q : ℕ) :
    ArithmeticKernel a (q*b) c where
  circuit := .comp (.bundle (fun s : Fin q =>
    .comp (cyclicInnerBlockInputCircuit a b c q s) K.circuit)) (blockOutputSumCircuit q a c)
  correct A B i j := by
    simp only [Circuit.eval_comp, blockOutputSumCircuit_eval, Circuit.eval_bundle,
      cyclicInnerBlockInputCircuit_eval, K.correct, Matrix.mul_apply,
      Matrix.submatrix_apply, id_eq]
    change (∑ s : Fin q, ∑ k : Fin b,
      A i (finProdFinEquiv (s,k))*B (finProdFinEquiv (s,k)) j) =
        ∑ k : Fin (q*b), A i k*B k j
    calc
      _ = ∑ x : Fin q × Fin b, A i (finProdFinEquiv x)*B (finProdFinEquiv x) j :=
        (Fintype.sum_prod_type _).symm
      _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ (fun x => rfl)

@[simp] theorem ArithmeticKernel.cyclicBlockInner_cost {a b c : ℕ}
    (K : ArithmeticKernel a b c) (q : ℕ) :
    (K.cyclicBlockInner q).cost = q*K.cost+q*a*c := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.cyclicBlockInner, cyclicInnerBlockInputCircuit]

def fixedCyclicHalfKernel
    (K : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ArithmeticKernel s b k :=
  (((K m).cyclicBlockInner 2).cyclicBlockRows
    (multiplicationBlockCount (max s m) m)).padShape
      (Fin.castLEEmb ((le_max_left s m).trans (multiplicationBlockCount_fits (max s m) m hm)))
      (Fin.castLEEmb hb) (Fin.castLEEmb hk)

theorem fixedCyclicHalfKernel_cost
    (K : ∀ m : ℕ, ArithmeticKernel m (width (1/2) m) m)
    (χ : ℕ → ℝ) (hχ : ∀ m, 1 ≤ χ m)
    (hK : ∀ m : ℕ, 1 ≤ m → ((K m).cost:ℝ) ≤ (m:ℝ)^2*χ m)
    (s m k b : ℕ) (hm : 0 < m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((fixedCyclicHalfKernel K s m k b hm hk hb).cost:ℝ) ≤
      8*χ m*(s+m:ℕ)*(m:ℝ) := by
  let N := max s m
  let P := (K m).cyclicBlockInner 2
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hχ0 : 0 ≤ χ m := (by norm_num : (0:ℝ) ≤ 1).trans (hχ m)
  have hNadd : (N:ℝ) ≤ (s+m:ℕ) := by exact_mod_cast (show max s m ≤ s+m by omega)
  have hP : (P.cost:ℝ) ≤ 4*χ m*(m:ℝ)^2 := by
    have hc := hK m hm
    have hh := mul_le_mul_of_nonneg_right (hχ m) (sq_nonneg (m:ℝ))
    dsimp only [P]
    rw [ArithmeticKernel.cyclicBlockInner_cost]
    push_cast
    nlinarith
  calc
    _ = (multiplicationBlockCount N m:ℝ)*(P.cost:ℝ) := by
      simp only [fixedCyclicHalfKernel, ArithmeticKernel.padShape_cost,
        ArithmeticKernel.cyclicBlockRows_cost, Nat.cast_mul, N, P]
    _ ≤ (2*(N:ℝ)/(m:ℝ))*(4*χ m*(m:ℝ)^2) :=
      mul_le_mul (multiplicationBlockCount_le N m hm (le_max_right _ _)) hP
        (Nat.cast_nonneg _) (by positivity)
    _ = 8*χ m*(N:ℝ)*(m:ℝ) := by field_simp; ring
    _ ≤ _ := by gcongr

end
end HierarchicalAbsoluteSpectral
