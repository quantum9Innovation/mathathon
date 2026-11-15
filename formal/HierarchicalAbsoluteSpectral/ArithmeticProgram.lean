import HierarchicalAbsoluteSpectral.DyadicNodes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
An operational model for the paper's exact real arithmetic. Programs execute
one field, nonnegative-square-root, or comparison instruction at a time.
`work` counts those executed instructions, including either comparison branch.
Tuple construction, projections and indexing carry no arithmetic cost.
Later algorithms must express their scalar arithmetic through these operations;
their cost bounds are proved for these programs, not assigned to value formulas.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

inductive ArithmeticOp where
  | add (x y : ℝ)
  | sub (x y : ℝ)
  | mul (x y : ℝ)
  | div (x y : ℝ)
  | sqrt (x : ℝ)

def ArithmeticOp.eval : ArithmeticOp → ℝ
  | .add x y => x+y
  | .sub x y => x-y
  | .mul x y => x*y
  | .div x y => x/y
  | .sqrt x => Real.sqrt x

def ArithmeticOp.admissible : ArithmeticOp → Prop
  | .div _ y => y ≠ 0
  | .sqrt x => 0 ≤ x
  | _ => True

inductive ArithmeticProgram (α : Type) where
  | pure (value : α)
  | step (op : ArithmeticOp) (next : ℝ → ArithmeticProgram α)
  | compare (x y : ℝ) (next : Bool → ArithmeticProgram α)
  | certifiedStep (op : ArithmeticOp) (next : {x : ℝ // x = op.eval} → ArithmeticProgram α)
  | branch (x y : ℝ) (ifLe : x ≤ y → ArithmeticProgram α) (ifGt : ¬x ≤ y → ArithmeticProgram α)

namespace ArithmeticProgram

def eval {α : Type} : ArithmeticProgram α → α
  | .pure a => a
  | .step op next => eval (next op.eval)
  | .compare x y next => eval (next (decide (x ≤ y)))
  | .certifiedStep op next => eval (next ⟨op.eval, rfl⟩)
  | .branch x y ifLe ifGt => if h : x ≤ y then eval (ifLe h) else eval (ifGt h)

def work {α : Type} : ArithmeticProgram α → ℕ
  | .pure _ => 0
  | .step op next => 1+work (next op.eval)
  | .compare x y next => 1+work (next (decide (x ≤ y)))
  | .certifiedStep op next => 1+work (next ⟨op.eval, rfl⟩)
  | .branch x y ifLe ifGt => 1+(if h : x ≤ y then work (ifLe h) else work (ifGt h))

/-- Every executed division and square root meets the field-model
precondition. This is an additional proof obligation on algorithm programs. -/
def admissible {α : Type} : ArithmeticProgram α → Prop
  | .pure _ => True
  | .step op next => op.admissible ∧ admissible (next op.eval)
  | .compare x y next => admissible (next (decide (x ≤ y)))
  | .certifiedStep op next => op.admissible ∧ admissible (next ⟨op.eval, rfl⟩)
  | .branch x y ifLe ifGt => if h : x ≤ y then admissible (ifLe h) else admissible (ifGt h)

def bind {α β : Type} : ArithmeticProgram α → (α → ArithmeticProgram β) → ArithmeticProgram β
  | .pure a, f => f a
  | .step op next, f => .step op (fun x => bind (next x) f)
  | .compare x y next, f => .compare x y (fun b => bind (next b) f)
  | .certifiedStep op next, f => .certifiedStep op (fun b => bind (next b) f)
  | .branch x y ifLe ifGt, f => .branch x y (fun h => bind (ifLe h) f) (fun h => bind (ifGt h) f)

instance : Monad ArithmeticProgram where
  pure := ArithmeticProgram.pure
  bind := ArithmeticProgram.bind

@[simp] theorem eval_pure {α : Type} (a : α) : (pure a : ArithmeticProgram α).eval = a := rfl
@[simp] theorem work_pure {α : Type} (a : α) : (pure a : ArithmeticProgram α).work = 0 := rfl
@[simp] theorem admissible_pure {α : Type} (a : α) : (pure a : ArithmeticProgram α).admissible := trivial

@[simp] theorem eval_bind {α β : Type} (p : ArithmeticProgram α) (f : α → ArithmeticProgram β) :
    (p >>= f).eval = (f p.eval).eval := by
  induction p with
  | pure a => rfl
  | step op next ih => exact ih op.eval
  | compare x y next ih => exact ih (decide (x ≤ y))
  | certifiedStep op next ih => exact ih ⟨op.eval, rfl⟩
  | branch x y ifLe ifGt ihLe ihGt =>
    by_cases h : x ≤ y
    · simpa only [Bind.bind, bind, eval, dif_pos h] using ihLe h
    · simpa only [Bind.bind, bind, eval, dif_neg h] using ihGt h

@[simp] theorem work_bind {α β : Type} (p : ArithmeticProgram α) (f : α → ArithmeticProgram β) :
    (p >>= f).work = p.work+(f p.eval).work := by
  induction p with
  | pure a => simp [ArithmeticProgram.work, ArithmeticProgram.eval, Bind.bind, bind]
  | step op next ih =>
    change 1+(next op.eval >>= f).work = (1+(next op.eval).work)+(f (next op.eval).eval).work
    rw [ih]
    omega
  | compare x y next ih =>
    change 1+(next (decide (x ≤ y)) >>= f).work =
      (1+(next (decide (x ≤ y))).work)+(f (next (decide (x ≤ y))).eval).work
    rw [ih]
    omega
  | certifiedStep op next ih =>
    change 1+(next ⟨op.eval, rfl⟩ >>= f).work =
      (1+(next ⟨op.eval, rfl⟩).work)+(f (next ⟨op.eval, rfl⟩).eval).work
    rw [ih]
    omega
  | branch x y ifLe ifGt ihLe ihGt =>
    by_cases h : x ≤ y
    · simpa only [Bind.bind, bind, work, eval, dif_pos h, Nat.add_assoc] using
        congrArg (fun n : ℕ => 1+n) (ihLe h)
    · simpa only [Bind.bind, bind, work, eval, dif_neg h, Nat.add_assoc] using
        congrArg (fun n : ℕ => 1+n) (ihGt h)

@[simp] theorem admissible_bind {α β : Type} (p : ArithmeticProgram α) (f : α → ArithmeticProgram β) :
    (p >>= f).admissible ↔ p.admissible ∧ (f p.eval).admissible := by
  induction p with
  | pure a => simp [admissible, eval, Bind.bind, bind]
  | step op next ih =>
    change (op.admissible ∧ (next op.eval >>= f).admissible) ↔
      (op.admissible ∧ (next op.eval).admissible) ∧ (f (next op.eval).eval).admissible
    rw [ih]
    exact and_assoc.symm
  | compare x y next ih => exact ih (decide (x ≤ y))
  | certifiedStep op next ih =>
    change (op.admissible ∧ (next ⟨op.eval, rfl⟩ >>= f).admissible) ↔
      (op.admissible ∧ (next ⟨op.eval, rfl⟩).admissible) ∧
        (f (next ⟨op.eval, rfl⟩).eval).admissible
    rw [ih]
    exact and_assoc.symm
  | branch x y ifLe ifGt ihLe ihGt =>
    by_cases h : x ≤ y
    · simpa only [Bind.bind, bind, admissible, eval, dif_pos h] using ihLe h
    · simpa only [Bind.bind, bind, admissible, eval, dif_neg h] using ihGt h

def execute (op : ArithmeticOp) : ArithmeticProgram ℝ := .step op .pure

@[simp] theorem eval_execute (op : ArithmeticOp) : (execute op).eval = op.eval := rfl
@[simp] theorem work_execute (op : ArithmeticOp) : (execute op).work = 1 := rfl
@[simp] theorem admissible_execute (op : ArithmeticOp) : (execute op).admissible ↔ op.admissible := by
  simp only [execute, admissible, and_true]

def add (x y : ℝ) : ArithmeticProgram ℝ := execute (.add x y)
def sub (x y : ℝ) : ArithmeticProgram ℝ := execute (.sub x y)
def mul (x y : ℝ) : ArithmeticProgram ℝ := execute (.mul x y)
def div (x y : ℝ) : ArithmeticProgram ℝ := execute (.div x y)
def sqrt (x : ℝ) : ArithmeticProgram ℝ := execute (.sqrt x)

@[simp] theorem eval_add (x y : ℝ) : (add x y).eval = x+y := rfl
@[simp] theorem eval_sub (x y : ℝ) : (sub x y).eval = x-y := rfl
@[simp] theorem eval_mul (x y : ℝ) : (mul x y).eval = x*y := rfl
@[simp] theorem eval_div (x y : ℝ) : (div x y).eval = x/y := rfl
@[simp] theorem eval_sqrt (x : ℝ) : (sqrt x).eval = Real.sqrt x := rfl
@[simp] theorem work_add (x y : ℝ) : (add x y).work = 1 := rfl
@[simp] theorem work_sub (x y : ℝ) : (sub x y).work = 1 := rfl
@[simp] theorem work_mul (x y : ℝ) : (mul x y).work = 1 := rfl
@[simp] theorem work_div (x y : ℝ) : (div x y).work = 1 := rfl
@[simp] theorem work_sqrt (x : ℝ) : (sqrt x).work = 1 := rfl

@[simp] theorem admissible_add (x y : ℝ) : (add x y).admissible := by trivial
@[simp] theorem admissible_sub (x y : ℝ) : (sub x y).admissible := by trivial
@[simp] theorem admissible_mul (x y : ℝ) : (mul x y).admissible := by trivial
@[simp] theorem admissible_div (x y : ℝ) : (div x y).admissible ↔ y ≠ 0 := by
  simp only [div, admissible_execute, ArithmeticOp.admissible]
@[simp] theorem admissible_sqrt (x : ℝ) : (sqrt x).admissible ↔ 0 ≤ x := by
  simp only [sqrt, admissible_execute, ArithmeticOp.admissible]

def complexAdd (z w : ℂ) : ArithmeticProgram ℂ := do
  let a ← add z.re w.re
  let b ← add z.im w.im
  pure ⟨a,b⟩

def complexSub (z w : ℂ) : ArithmeticProgram ℂ := do
  let a ← sub z.re w.re
  let b ← sub z.im w.im
  pure ⟨a,b⟩

def complexMul (z w : ℂ) : ArithmeticProgram ℂ := do
  let a ← mul z.re w.re
  let b ← mul z.im w.im
  let c ← mul z.re w.im
  let d ← mul z.im w.re
  let u ← sub a b
  let v ← add c d
  pure ⟨u,v⟩

@[simp] theorem eval_complexAdd (z w : ℂ) : (complexAdd z w).eval = z+w := by
  apply Complex.ext <;> simp [complexAdd]
@[simp] theorem eval_complexSub (z w : ℂ) : (complexSub z w).eval = z-w := by
  apply Complex.ext <;> simp [complexSub]
@[simp] theorem eval_complexMul (z w : ℂ) : (complexMul z w).eval = z*w := by
  apply Complex.ext <;> simp [complexMul, Complex.mul_re, Complex.mul_im]
@[simp] theorem work_complexAdd (z w : ℂ) : (complexAdd z w).work = 2 := by simp [complexAdd]
@[simp] theorem work_complexSub (z w : ℂ) : (complexSub z w).work = 2 := by simp [complexSub]
@[simp] theorem work_complexMul (z w : ℂ) : (complexMul z w).work = 6 := by simp [complexMul]
@[simp] theorem admissible_complexAdd (z w : ℂ) : (complexAdd z w).admissible := by simp [complexAdd]
@[simp] theorem admissible_complexSub (z w : ℂ) : (complexSub z w).admissible := by simp [complexSub]
@[simp] theorem admissible_complexMul (z w : ℂ) : (complexMul z w).admissible := by simp [complexMul]

def tabulate {α : Type} : (n : ℕ) → (Fin n → ArithmeticProgram α) → ArithmeticProgram (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n+1, f => do
      let a ← f 0
      let as ← tabulate n (fun i => f i.succ)
      pure (Fin.cons a as)

@[simp] theorem eval_tabulate {α : Type} (n : ℕ) (f : Fin n → ArithmeticProgram α) :
    (tabulate n f).eval = fun i => (f i).eval := by
  induction n with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    simp only [tabulate, eval_bind, eval_pure, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem work_tabulate {α : Type} (n : ℕ) (f : Fin n → ArithmeticProgram α) :
    (tabulate n f).work = ∑ i : Fin n, (f i).work := by
  induction n with
  | zero => simp [tabulate]
  | succ n ih =>
    simp only [tabulate, work_bind, work_pure, add_zero, ih, Fin.sum_univ_succ]

@[simp] theorem admissible_tabulate {α : Type} (n : ℕ) (f : Fin n → ArithmeticProgram α) :
    (tabulate n f).admissible ↔ ∀ i : Fin n, (f i).admissible := by
  induction n with
  | zero => simp [tabulate]
  | succ n ih =>
    simp only [tabulate, admissible_bind, admissible_pure, and_true, ih, Fin.forall_fin_succ]

/-- Attach the proved value to a computed result. The compilation replaces
raw instructions by certified instructions with the identical operational
cost. This permits dependent termination proofs without an arithmetic oracle. -/
def certify {α : Type} : (p : ArithmeticProgram α) → ArithmeticProgram {x : α // x = p.eval}
  | .pure a => .pure ⟨a, rfl⟩
  | .step op next => .certifiedStep op (fun x => do
      let a ← certify (next x.val)
      ArithmeticProgram.pure ⟨a.val, by simpa only [eval, x.property] using a.property⟩)
  | .compare x y next => .branch x y
      (fun h => do
        let a ← certify (next true)
        ArithmeticProgram.pure ⟨a.val, by simpa [eval, h] using a.property⟩)
      (fun h => do
        let a ← certify (next false)
        ArithmeticProgram.pure ⟨a.val, by simpa [eval, h] using a.property⟩)
  | .certifiedStep op next => .certifiedStep op (fun x => do
      let a ← certify (next x)
      ArithmeticProgram.pure ⟨a.val, by
        have hx : x = ⟨op.eval, rfl⟩ := Subtype.ext x.property
        simpa only [eval, hx] using a.property⟩)
  | .branch x y ifLe ifGt => .branch x y
      (fun h => do
        let a ← certify (ifLe h)
        ArithmeticProgram.pure ⟨a.val, by simpa only [eval, dif_pos h] using a.property⟩)
      (fun h => do
        let a ← certify (ifGt h)
        ArithmeticProgram.pure ⟨a.val, by simpa only [eval, dif_neg h] using a.property⟩)

@[simp] theorem certify_eval {α : Type} (p : ArithmeticProgram α) : (certify p).eval.val = p.eval :=
  (certify p).eval.property

@[simp] theorem certify_work {α : Type} (p : ArithmeticProgram α) : (certify p).work = p.work := by
  induction p with
  | pure a => rfl
  | step op next ih => simp only [certify, work, work_bind, add_zero, ih]
  | compare x y next ih =>
    by_cases h : x ≤ y <;> simp [certify, work, h, ih]
  | certifiedStep op next ih => simp only [certify, work, work_bind, add_zero, ih]
  | branch x y ifLe ifGt ihLe ihGt =>
    by_cases h : x ≤ y <;> simp [certify, work, h, ihLe, ihGt]

@[simp] theorem certify_admissible {α : Type} (p : ArithmeticProgram α) :
    (certify p).admissible ↔ p.admissible := by
  induction p with
  | pure a => rfl
  | step op next ih => simp only [certify, admissible, admissible_bind, and_true, ih]
  | compare x y next ih =>
    by_cases h : x ≤ y <;> simp [certify, admissible, h, ih]
  | certifiedStep op next ih =>
    simp only [certify, admissible, admissible_bind, and_true, ih]
  | branch x y ifLe ifGt ihLe ihGt =>
    by_cases h : x ≤ y <;> simp [certify, admissible, h, ihLe, ihGt]

end ArithmeticProgram
end
end HierarchicalAbsoluteSpectral
