import HierarchicalAbsoluteSpectral.StrongFilterSearch
import HierarchicalAbsoluteSpectral.StrongFilterPhysical
import HierarchicalAbsoluteSpectral.MatrixAction
import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram

/-! Counted strong polynomial action and actual physical range extraction.
The executable lift uses the carried operator and never inverts a fine factor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix Polynomial Polynomial.Chebyshev
open ArithmeticProgram hiding pure
variable {k b n : ℕ}

def scalarChebyshevPairProgram (x : ℝ) : ℕ → ArithmeticProgram (ℝ×ℝ)
  | 0 => .pure (x,1)
  | v+1 => do
      let p ← scalarChebyshevPairProgram x v
      let z ← chebyshevNextProgram x p.1 p.2
      ArithmeticProgram.pure (p.2,z)

theorem scalarChebyshevPairProgram_eval (x : ℝ) (v : ℕ) :
    (scalarChebyshevPairProgram x v).eval=
      ((T ℝ ((v:ℤ)-1)).eval x,(T ℝ (v:ℤ)).eval x) := by
  induction v with
  | zero => simp [scalarChebyshevPairProgram]
  | succ v ih =>
      simp only [scalarChebyshevPairProgram, eval_bind, eval_pure, ih, chebyshevNextProgram_eval,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, T_add_one,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

@[simp] theorem scalarChebyshevPairProgram_work (x : ℝ) (v : ℕ) :
    (scalarChebyshevPairProgram x v).work=3*v := by
  induction v with
  | zero => rfl
  | succ v ih => simp [scalarChebyshevPairProgram, ih]; omega

theorem scalarChebyshevPairProgram_admissible (x : ℝ) (v : ℕ) :
    (scalarChebyshevPairProgram x v).admissible := by
  induction v with
  | zero => trivial
  | succ v ih => simp [scalarChebyshevPairProgram, ih, chebyshevNextProgram_admissible]

def strongScaleProgram (α : ℝ) (v : ℕ) : ArithmeticProgram (ℝ×ℝ) := do
  let a ← add 1 α
  let c ← div 2 a
  let x ← strongCoordinateProgram α
  let d ← scalarChebyshevPairProgram x v
  let z ← div 1 d.2
  ArithmeticProgram.pure (c,z)

@[simp] theorem strongScaleProgram_eval (α : ℝ) (v : ℕ) :
    (strongScaleProgram α v).eval=(2/(1+α),(strongFilterDenominator α v)⁻¹) := by
  simp [strongScaleProgram, scalarChebyshevPairProgram_eval, strongFilterDenominator]

@[simp] theorem strongScaleProgram_work (α : ℝ) (v : ℕ) :
    (strongScaleProgram α v).work=9+3*v := by simp [strongScaleProgram]; omega

theorem strongScaleProgram_admissible (α : ℝ) (v : ℕ) (hα : 0<α) :
    (strongScaleProgram α v).admissible := by
  have hd : strongFilterDenominator α v≠0 := by
    have := strongFilterDenominator_ge_one α hα v
    linarith
  simp [strongScaleProgram, scalarChebyshevPairProgram_admissible, strongCoordinateProgram_admissible α hα,
    scalarChebyshevPairProgram_eval,
    (by positivity : (1:ℝ)+α≠0)]
  exact hd

theorem singleChebyshev_sum (v : ℕ) :
    (∑ j ∈ Finset.range (v+1), (if (j:ℤ)=(v:ℤ) then (1:ℝ) else 0) • T ℝ (j:ℤ))=T ℝ (v:ℤ) := by
  simp only [Int.natCast_inj, ite_smul, one_smul, zero_smul]
  simp

def MatrixAction.singleChebyshev {A : Core k} (P : MatrixAction A b) (v : ℕ) :
    MatrixAction (aeval A (T ℝ (v:ℤ))) b where
  program V := chebyshevActionProgram P.program (fun j => if j=(v:ℤ) then 1 else 0) (v+1) V
  correct V := by
    rw [chebyshevActionProgram_eval P.program A P.correct, singleChebyshev_sum]
  valid V := chebyshevActionProgram_admissible P.program P.valid _ _ V
  cost := (v+1)*(P.cost+4*k*b)
  work_le V := chebyshevActionProgram_work P.program P.cost P.work_le _ _ V

theorem strongFilterPolynomial_aeval (A : Core k) (α : ℝ) (v : ℕ) :
    aeval A (strongFilterPolynomial α v)=
      (strongFilterDenominator α v)⁻¹ • aeval ((2/(1+α)) • A-1) (T ℝ (v:ℤ)) := by
  simp only [strongFilterPolynomial, map_mul, Polynomial.aeval_C, aeval_comp,
    map_sub, map_mul, aeval_X, map_one, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul]

def strongFilterAction {A : Core k} (P : MatrixAction A b) (α : ℝ) (v : ℕ) (hα : 0<α) :
    MatrixAction (aeval A (strongFilterPolynomial α v)) b where
  program V := do
    let z ← strongScaleProgram α v
    let Y ← (((P.scale z.1).sub (MatrixAction.identity k b)).singleChebyshev v).program V
    blockScaleProgram z.2 Y
  correct V := by
    simp only [eval_bind, MatrixAction.correct, strongScaleProgram_eval, blockScaleProgram_eval]
    rw [strongFilterPolynomial_aeval, Matrix.smul_mul]
  valid V := by
    simp only [admissible_bind, MatrixAction.valid, blockScaleProgram_admissible, and_true]
    exact strongScaleProgram_admissible α v hα
  cost := 9+3*v+(v+1)*(P.cost+6*k*b)+k*b
  work_le V := by
    simp only [work_bind, strongScaleProgram_work, blockScaleProgram_work]
    have hs := (((P.scale (strongScaleProgram α v).eval.1).sub
      (MatrixAction.identity k b)).singleChebyshev v).work_le V
    have hc : (((P.scale (strongScaleProgram α v).eval.1).sub
        (MatrixAction.identity k b)).singleChebyshev v).cost=(v+1)*(P.cost+6*k*b) := by
      dsimp only [MatrixAction.singleChebyshev, MatrixAction.sub, MatrixAction.scale,
        MatrixAction.identity]
      ring
    rw [hc] at hs
    omega

def OrthogonalRange.cast {Y Z : Matrix (Fin n) (Fin b) ℝ}
    (out : OrthogonalRange Y) (h : Y=Z) : OrthogonalRange Z := h ▸ out

def strongPhysicalRangeProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {L : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A b) (PL : MatrixAction L b)
    (α : ℝ) (v : ℕ) (hα : 0<α) (Ξ : Matrix (Fin k) (Fin b) ℝ) :
    ArithmeticProgram (OrthogonalRange (L*(aeval A (strongFilterPolynomial α v)*Ξ))) := do
  let F ← ((strongFilterAction P α v hα).program Ξ).certify
  let Y ← (PL.program F.val).certify
  let out ← orthogonalRangeProgram kernels Y.val
  ArithmeticProgram.pure (out.cast (by rw [Y.property, PL.correct, F.property, MatrixAction.correct]))

theorem strongPhysicalRangeProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {L : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A b) (PL : MatrixAction L b)
    (α : ℝ) (v : ℕ) (hα : 0<α) (Ξ : Matrix (Fin k) (Fin b) ℝ) :
    (strongPhysicalRangeProgram kernels P PL α v hα Ξ).admissible := by
  simp only [strongPhysicalRangeProgram, admissible_bind, certify_admissible,
    MatrixAction.valid, orthogonalRangeProgram_admissible, admissible_pure, and_self]

end
end HierarchicalAbsoluteSpectral
