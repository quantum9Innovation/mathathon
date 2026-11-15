import HierarchicalAbsoluteSpectral.CoarseAlgebraGaussianInertia
import HierarchicalAbsoluteSpectral.CoarseAlgebraInertiaSupportProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n : ℕ}

@[simp] theorem CongruenceDiagonalData.cast_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    {D E : Matrix ι ι ℝ} (out : CongruenceDiagonalData D) (h : D = E) :
    (out.cast h).basis = out.basis := by cases h; rfl

@[simp] theorem CongruenceDiagonalData.cast_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
    {D E : Matrix ι ι ℝ} (out : CongruenceDiagonalData D) (h : D = E) :
    (out.cast h).inverse = out.inverse := by cases h; rfl

def inertiaLiftProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (out : FiniteCongruenceDiagonal support.compressed) :
    ArithmeticProgram (FiniteCongruenceDiagonal D) := do
  let blockP : Core n := (Matrix.fromBlocks out.basis
    (0 : Matrix (Fin support.dimension) (Fin support.nullity) ℝ) 0 (1 : Core support.nullity)).submatrix
      support.indexEquiv.symm support.indexEquiv.symm
  let blockV : Core n := (Matrix.fromBlocks out.inverse
    (0 : Matrix (Fin support.dimension) (Fin support.nullity) ℝ) 0 (1 : Core support.nullity)).submatrix
      support.indexEquiv.symm support.indexEquiv.symm
  let P ← certify ((kernels n n n).program support.frame blockP)
  let V ← certify ((kernels n n n).program blockV support.frameᵀ)
  let expected := support.lift out
  have hP : P.val = expected.basis := by
    simp only [P.property,ArithmeticKernel.program_eval,expected,InertiaSupport.lift,
      CongruenceDiagonalData.toFinite,CongruenceDiagonalData.conjugate,
      CongruenceDiagonalData.cast_basis,CongruenceDiagonalData.reindex,
      CongruenceDiagonalData.blockZero,FiniteCongruenceDiagonal.toData,blockP]
  have hV : V.val = expected.inverse := by
    simp only [V.property,ArithmeticKernel.program_eval,expected,InertiaSupport.lift,
      CongruenceDiagonalData.toFinite,CongruenceDiagonalData.conjugate,
      CongruenceDiagonalData.cast_inverse,CongruenceDiagonalData.reindex,
      CongruenceDiagonalData.blockZero,FiniteCongruenceDiagonal.toData,blockV]
  ArithmeticProgram.pure (expected.replace P.val V.val hP hV)

theorem inertiaLiftProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (out : FiniteCongruenceDiagonal support.compressed) :
    (inertiaLiftProgram kernels support out).admissible := by
  simp only [inertiaLiftProgram,admissible_bind,certify_admissible,
    ArithmeticKernel.program_admissible,admissible_pure,and_self]

theorem inertiaLiftProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (out : FiniteCongruenceDiagonal support.compressed) :
    (inertiaLiftProgram kernels support out).work = 2*(kernels n n n).cost := by
  simp only [inertiaLiftProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure]
  omega

/-- Exact inertia, including every singular shift. Each `some` carries an
ordinary square congruence certificate for D with its zero block included.
The fresh ambient Gaussian array has n² entries on every input. -/
def singularInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal D)) := do
  let support ← inertiaSupportProgram kernels D hD
  let out? ← gaussianReducedInertiaProgram kernels support hD g
  match out? with
  | none => ArithmeticProgram.pure none
  | some out => do
    let lifted ← inertiaLiftProgram kernels support out
    ArithmeticProgram.pure (some lifted)

theorem singularInertiaProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    (singularInertiaProgram kernels n D hD g).admissible := by
  simp only [singularInertiaProgram,admissible_bind,inertiaSupportProgram_admissible,
    gaussianReducedInertiaProgram,congruenceInertiaProgram_admissible,true_and]
  split
  · trivial
  · simp only [admissible_bind,inertiaLiftProgram_admissible,admissible_pure,and_self]

theorem singularInertiaProgram_success_ae (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) :
    ∀ᵐ g ∂gaussianVector (n*n), ∃ out, (singularInertiaProgram kernels n D hD g).eval = some out := by
  let support := (inertiaSupportProgram kernels D hD).eval
  have he := gaussianReducedInertiaProgram_success_ae kernels support hD
  filter_upwards [he] with g hg
  obtain ⟨out,ho⟩ := hg
  unfold singularInertiaProgram
  rw [eval_bind,eval_bind,ho,eval_bind,eval_pure]
  exact ⟨_,rfl⟩

end
end HierarchicalAbsoluteSpectral
