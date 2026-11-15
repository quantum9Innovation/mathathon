import HierarchicalAbsoluteSpectral.ArithmeticProgram
import Matmul.UniversalProgram

/-!
Translation from universal arithmetic circuits to the same exact-real program
model used for the hierarchy. The translation preserves every gate count and
materializes shared intermediate values once. In particular, a fast circuit
bound is a bound for actual arithmetic instructions, not an assigned counter.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure
open scoped BigOperators

def finiteTabulateProgram {I α : Type} [Fintype I]
    (f : I → ArithmeticProgram α) : ArithmeticProgram (I → α) := do
  let a ← tabulate (Fintype.card I) (fun i => f ((Fintype.equivFin I).symm i))
  ArithmeticProgram.pure (fun i => a ((Fintype.equivFin I) i))

@[simp] theorem finiteTabulateProgram_eval {I α : Type} [Fintype I]
    (f : I → ArithmeticProgram α) :
    (finiteTabulateProgram f).eval = fun i => (f i).eval := by
  simp [finiteTabulateProgram]

@[simp] theorem finiteTabulateProgram_work {I α : Type} [Fintype I]
    (f : I → ArithmeticProgram α) :
    (finiteTabulateProgram f).work = ∑ i, (f i).work := by
  simp only [finiteTabulateProgram, work_bind, work_pure, add_zero, work_tabulate]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

@[simp] theorem finiteTabulateProgram_admissible {I α : Type} [Fintype I]
    (f : I → ArithmeticProgram α) :
    (finiteTabulateProgram f).admissible ↔ ∀ i, (f i).admissible := by
  simp only [finiteTabulateProgram, admissible_bind, admissible_pure, and_true,
    admissible_tabulate]
  constructor
  · intro h i
    simpa using h ((Fintype.equivFin I) i)
  · intro h i
    exact h _

open Matmul.UniversalProgram

def circuitProgram : {I O : Type} → Circuit I O → (I → ℝ) → ArithmeticProgram (O → ℝ)
  | _, _, .wire select, input => .pure (fun o => input (select o))
  | _, _, .zero, _ => .pure (fun _ => 0)
  | _, _, .add, input => do
      let x ← add (input false) (input true)
      ArithmeticProgram.pure (fun _ => x)
  | _, _, .neg, input => do
      let x ← sub 0 (input PUnit.unit)
      ArithmeticProgram.pure (fun _ => x)
  | _, _, .mul, input => do
      let x ← mul (input false) (input true)
      ArithmeticProgram.pure (fun _ => x)
  | _, _, @Circuit.comp _ _ _ inst first second, input =>
      letI := inst
      do
        let middle ← circuitProgram first input
        circuitProgram second middle
  | _, _, .pair left right, input => do
      let a ← circuitProgram left input
      let b ← circuitProgram right input
      ArithmeticProgram.pure (Sum.elim a b)
  | _, _, @Circuit.bundle _ J _ inst branches, input =>
      letI := inst
      do
        let outputs ← finiteTabulateProgram (fun j : J => circuitProgram (branches j) input)
        ArithmeticProgram.pure (fun p => outputs p.1 p.2)

theorem circuitProgram_eval {I O : Type} (c : Circuit I O) :
    ∀ input, (circuitProgram c input).eval = c.eval input := by
  induction c with
  | wire select => intro input; rfl
  | zero => intro input; rfl
  | add => intro input; simp [circuitProgram, Circuit.eval]
  | neg => intro input; simp [circuitProgram, Circuit.eval]
  | mul => intro input; simp [circuitProgram, Circuit.eval]
  | comp first second ihfirst ihsecond =>
      intro input
      simp [circuitProgram, Circuit.eval, ihfirst, ihsecond]
  | pair left right ihleft ihright =>
      intro input
      simp [circuitProgram, Circuit.eval, ihleft, ihright]
  | bundle branches ih =>
      intro input
      simp [circuitProgram, Circuit.eval, ih]

theorem circuitProgram_work {I O : Type} (c : Circuit I O) :
    ∀ input, (circuitProgram c input).work = c.cost := by
  induction c with
  | wire select => intro input; rfl
  | zero => intro input; rfl
  | add => intro input; simp [circuitProgram]
  | neg => intro input; simp [circuitProgram]
  | mul => intro input; simp [circuitProgram]
  | comp first second ihfirst ihsecond =>
      intro input
      simp [circuitProgram, ihfirst, ihsecond]
  | pair left right ihleft ihright =>
      intro input
      simp [circuitProgram, ihleft, ihright]
  | bundle branches ih =>
      intro input
      simp [circuitProgram, ih]

theorem circuitProgram_admissible {I O : Type} (c : Circuit I O) :
    ∀ input, (circuitProgram c input).admissible := by
  induction c with
  | wire select => intro input; trivial
  | zero => intro input; trivial
  | add => intro input; simp [circuitProgram]
  | neg => intro input; simp [circuitProgram]
  | mul => intro input; simp [circuitProgram]
  | comp first second ihfirst ihsecond =>
      intro input
      simp [circuitProgram, ihfirst, ihsecond]
  | pair left right ihleft ihright =>
      intro input
      simp [circuitProgram, ihleft, ihright]
  | bundle branches ih =>
      intro input
      simp [circuitProgram, ih]

end
end HierarchicalAbsoluteSpectral
