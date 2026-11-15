import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelPadding
import HierarchicalAbsoluteSpectral.CoarseAlgebraClassicalKernel

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.UniversalProgram
open scoped BigOperators

def rowBlockInputCircuit (q m p : ℕ) (s : Fin q) :
    Circuit ((Fin (q*m) × Fin m) ⊕ (Fin m × Fin p))
      ((Fin m × Fin m) ⊕ (Fin m × Fin p)) :=
  .pair (.wire (fun x => Sum.inl (finProdFinEquiv (s,x.1),x.2)))
    (.wire Sum.inr)

theorem rowBlockInputCircuit_eval (q m p : ℕ) (s : Fin q)
    (A : Matrix (Fin (q*m)) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (rowBlockInputCircuit q m p s).eval (matrixCircuitInput A B) =
      matrixCircuitInput (A.submatrix (fun i => finProdFinEquiv (s,i)) id) B := by
  funext x
  cases x <;> rfl

def ArithmeticKernel.blockRows {m p : ℕ} (K : ArithmeticKernel m m p) (q : ℕ) :
    ArithmeticKernel (q*m) m p where
  circuit := .comp (.bundle (fun s : Fin q =>
    .comp (rowBlockInputCircuit q m p s) K.circuit))
    (.wire (fun x : Fin (q*m) × Fin p =>
      ((finProdFinEquiv.symm x.1).1,((finProdFinEquiv.symm x.1).2,x.2))))
  correct A B i j := by
    simp only [Circuit.eval_comp, Circuit.eval_wire, Circuit.eval_bundle,
      rowBlockInputCircuit_eval, K.correct]
    change ∑ x, A (finProdFinEquiv (finProdFinEquiv.symm i)) x * B x j = (A*B) i j
    rw [Equiv.apply_symm_apply, Matrix.mul_apply]

@[simp] theorem ArithmeticKernel.blockRows_cost {m p : ℕ}
    (K : ArithmeticKernel m m p) (q : ℕ) : (K.blockRows q).cost = q*K.cost := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.blockRows, rowBlockInputCircuit]

def innerBlockInputCircuit (q m p : ℕ) (s : Fin q) :
    Circuit ((Fin m × Fin (q*m)) ⊕ (Fin (q*m) × Fin p))
      ((Fin m × Fin m) ⊕ (Fin m × Fin p)) :=
  .pair (.wire (fun x => Sum.inl (x.1,finProdFinEquiv (s,x.2))))
    (.wire (fun x => Sum.inr (finProdFinEquiv (s,x.1),x.2)))

theorem innerBlockInputCircuit_eval (q m p : ℕ) (s : Fin q)
    (A : Matrix (Fin m) (Fin (q*m)) ℝ) (B : Matrix (Fin (q*m)) (Fin p) ℝ) :
    (innerBlockInputCircuit q m p s).eval (matrixCircuitInput A B) =
      matrixCircuitInput (A.submatrix id (fun i => finProdFinEquiv (s,i)))
        (B.submatrix (fun i => finProdFinEquiv (s,i)) id) := by
  funext x
  cases x <;> rfl

def blockOutputSumCircuit (q m p : ℕ) :
    Circuit (Fin q × (Fin m × Fin p)) (Fin m × Fin p) :=
  .comp (.bundle (fun x : Fin m × Fin p =>
    finiteCircuitSum q (fun s => .wire (fun _ => (s,x)))))
    (.wire (fun x => (x,PUnit.unit)))

theorem blockOutputSumCircuit_eval (q m p : ℕ)
    (input : Fin q × (Fin m × Fin p) → ℝ) (x : Fin m × Fin p) :
    (blockOutputSumCircuit q m p).eval input x = ∑ s, input (s,x) := by
  simp [blockOutputSumCircuit, finiteCircuitSum_eval]

@[simp] theorem blockOutputSumCircuit_cost (q m p : ℕ) :
    (blockOutputSumCircuit q m p).cost = q*m*p := by
  simp [blockOutputSumCircuit, finiteCircuitSum_cost]
  ring

def ArithmeticKernel.blockInner {m p : ℕ} (K : ArithmeticKernel m m p) (q : ℕ) :
    ArithmeticKernel m (q*m) p where
  circuit := .comp (.bundle (fun s : Fin q =>
    .comp (innerBlockInputCircuit q m p s) K.circuit)) (blockOutputSumCircuit q m p)
  correct A B i j := by
    simp only [Circuit.eval_comp, blockOutputSumCircuit_eval, Circuit.eval_bundle,
      innerBlockInputCircuit_eval, K.correct, Matrix.mul_apply, Matrix.submatrix_apply,
      id_eq]
    change (∑ s : Fin q, ∑ k : Fin m,
      A i (finProdFinEquiv (s,k))*B (finProdFinEquiv (s,k)) j) =
        ∑ k : Fin (q*m), A i k*B k j
    calc
      _ = ∑ x : Fin q × Fin m, A i (finProdFinEquiv x)*B (finProdFinEquiv x) j :=
        (Fintype.sum_prod_type _).symm
      _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ (fun x => rfl)

@[simp] theorem ArithmeticKernel.blockInner_cost {m p : ℕ}
    (K : ArithmeticKernel m m p) (q : ℕ) :
    (K.blockInner q).cost = q*K.cost+q*m*p := by
  simp [ArithmeticKernel.cost, ArithmeticKernel.blockInner, innerBlockInputCircuit]

def multiplicationBlockCount (N m : ℕ) : ℕ := N/m+1

theorem multiplicationBlockCount_fits (N m : ℕ) (hm : 0 < m) :
    N ≤ multiplicationBlockCount N m*m := by
  have hmod := Nat.mod_lt N hm
  have hdiv := Nat.div_add_mod N m
  dsimp [multiplicationBlockCount]
  nlinarith

def ArithmeticKernel.tall {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) : ArithmeticKernel N m p :=
  (K.blockRows (multiplicationBlockCount N m)).padShape
    (Fin.castLEEmb (multiplicationBlockCount_fits N m hm))
    (Function.Embedding.refl _) (Function.Embedding.refl _)

@[simp] theorem ArithmeticKernel.tall_cost {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) :
    (K.tall N hm).cost = multiplicationBlockCount N m*K.cost := by
  simp [ArithmeticKernel.tall]

def ArithmeticKernel.longInner {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) : ArithmeticKernel m N p :=
  (K.blockInner (multiplicationBlockCount N m)).padShape
    (Function.Embedding.refl _)
    (Fin.castLEEmb (multiplicationBlockCount_fits N m hm))
    (Function.Embedding.refl _)

@[simp] theorem ArithmeticKernel.longInner_cost {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) :
    (K.longInner N hm).cost =
      multiplicationBlockCount N m*K.cost+multiplicationBlockCount N m*m*p := by
  simp [ArithmeticKernel.longInner]

theorem multiplicationBlockCount_le (N m : ℕ) (hm : 0 < m) (hNm : m ≤ N) :
    (multiplicationBlockCount N m:ℝ) ≤ 2*(N:ℝ)/(m:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hdiv : (N/m:ℕ) ≤ (N:ℝ)/(m:ℝ) := Nat.cast_div_le
  have hone : (1:ℝ) ≤ (N:ℝ)/(m:ℝ) := (le_div_iff₀ hmR).mpr (by simpa using hNmR)
  simp only [multiplicationBlockCount,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ (N:ℝ)/(m:ℝ)+1 := by linarith
    _ ≤ 2*((N:ℝ)/(m:ℝ)) := by linarith
    _ = _ := by ring

theorem ArithmeticKernel.tall_cost_bound {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) (hNm : m ≤ N) (C E : ℝ) (hC : 0 ≤ C)
    (hK : (K.cost:ℝ) ≤ C*(m:ℝ)^E) :
    ((K.tall N hm).cost:ℝ) ≤ 2*C*(N:ℝ)*(m:ℝ)^(E-1) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hp : (m:ℝ)^E = (m:ℝ)*(m:ℝ)^(E-1) := by
    calc
      _ = (m:ℝ)^(1+(E-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hmR,Real.rpow_one]
  rw [ArithmeticKernel.tall_cost,Nat.cast_mul]
  calc
    _ ≤ (2*(N:ℝ)/(m:ℝ))*(C*(m:ℝ)^E) :=
      mul_le_mul (multiplicationBlockCount_le N m hm hNm) hK (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [hp]; field_simp

theorem ArithmeticKernel.longInner_cost_bound {m p : ℕ} (K : ArithmeticKernel m m p)
    (N : ℕ) (hm : 0 < m) (hNm : m ≤ N) (C E : ℝ) (hC : 0 ≤ C)
    (hK : (K.cost:ℝ) ≤ C*(m:ℝ)^E) :
    ((K.longInner N hm).cost:ℝ) ≤
      2*C*(N:ℝ)*(m:ℝ)^(E-1)+2*(N:ℝ)*(p:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hs : (multiplicationBlockCount N m:ℝ)*(m:ℝ)*(p:ℝ) ≤
      2*(N:ℝ)*(p:ℝ) := by
    calc
      _ ≤ (2*(N:ℝ)/(m:ℝ))*(m:ℝ)*(p:ℝ) := by
        gcongr
        exact multiplicationBlockCount_le N m hm hNm
      _ = _ := by field_simp
  rw [ArithmeticKernel.longInner_cost,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul]
  have ht := K.tall_cost_bound N hm hNm C E hC hK
  simp only [ArithmeticKernel.tall_cost,Nat.cast_mul] at ht
  exact add_le_add ht hs

end
end HierarchicalAbsoluteSpectral
