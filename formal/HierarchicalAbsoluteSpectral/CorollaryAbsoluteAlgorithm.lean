import HierarchicalAbsoluteSpectral.CorollaryAbsoluteTape
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteDoubling

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

/-- A constructed finite fallback. It executes the supplied verified
multiplication kernel and returns both original factors and the dense product. -/
def absoluteFullProductProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    ArithmeticProgram (FixedRankOutput n p m) := do
  let C ← ((kernels n m p).program A B).certify
  .pure { width := m
          width_le := le_rfl
          left := A
          right := B
          product := C.val
          product_eq := C.property.trans (ArithmeticKernel.program_eval _ _ _) }

theorem absoluteFullProductProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (absoluteFullProductProgram kernels A B).admissible := by
  simp only [absoluteFullProductProgram,admissible_bind,certify_admissible,
    ArithmeticKernel.program_admissible,admissible_pure,and_self]

@[simp] theorem absoluteFullProductProgram_product (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (absoluteFullProductProgram kernels A B).eval.product=A*B := by
  simp only [absoluteFullProductProgram,eval_bind,certify_eval,ArithmeticKernel.program_eval,eval_pure]

@[simp] theorem absoluteFullProductProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (absoluteFullProductProgram kernels A B).work=(kernels n m p).cost := by
  simp only [absoluteFullProductProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,Nat.add_zero]

/-- The full-support projection branch precedes the r+1 query. A below
decision advances; either accepted decision executes a fresh carried filter. -/
def absoluteAttemptProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    ArithmeticProgram (Option (FixedRankOutput n p s)) :=
  if hrank : C.pair.dimension ≤ s then do
    let out ← supportExactOutputProgram kernels I.A I.B (mainSupportAction kernels I S C _) hrank
    .pure (some out)
  else do
    let decision ← absolutePositiveQueryProgram kernels I S C s (Nat.lt_of_not_ge hrank) t z.1 z.2.1
    match decision with
    | .below => .pure none
    | .above | .near => do
      let out ← absoluteStrongThresholdProgram kernels I S C s (by omega) t z.2.2
      .pure (some out)

theorem absoluteAttemptProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    (absoluteAttemptProgram kernels I S C s t z).admissible := by
  unfold absoluteAttemptProgram
  split_ifs
  · simp only [admissible_bind,supportExactOutputProgram_admissible,admissible_pure,and_self]
  · simp only [admissible_bind,absolutePositiveQueryProgram_admissible,true_and]
    split
    · trivial
    all_goals simp only [admissible_bind,absoluteStrongThresholdProgram_admissible,admissible_pure,and_self]

def absoluteCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) (z : AbsoluteCoreTape I) : ArithmeticProgram (AbsoluteOutput n p m) :=
  absoluteDoublingProgram (fun s =>
    if hs : s ≤ m then absoluteAttemptProgram kernels I.seed S C s t
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    else .pure none) (absoluteFullProductProgram kernels I.A I.B)

theorem absoluteCoreProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : {t : ℝ // 0 < t}) (z : AbsoluteCoreTape I) :
    (absoluteCoreProgram kernels I S C t z).admissible := by
  apply absoluteDoublingLoop_admissible
  · intro s
    split_ifs
    · exact absoluteAttemptProgram_admissible kernels I.seed S C s t _
    · trivial
  · exact absoluteFullProductProgram_admissible kernels I.A I.B

/-- No slack rank is supplied or evaluated. The threshold, sketches,
support, queries, carried ranges and fallback are all executed programs. -/
def absoluteAlgorithmProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ArithmeticProgram (AbsoluteOutput n p m) := do
  let t ← (absoluteThresholdProgram I).certify
  have ht : 0 < t.val := by rw [t.property,absoluteThresholdProgram_eval]; exact absoluteThreshold_positive I
  let sketches ← mainSketchProgram I.seed g.1
  let support ← coarseSupportProgram kernels sketches.initialA sketches.initialB
  absoluteCoreProgram kernels I sketches support ⟨t.val,ht⟩ g.2

theorem absoluteAlgorithmProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    (absoluteAlgorithmProgram kernels I g).admissible := by
  simp only [absoluteAlgorithmProgram,admissible_bind,certify_admissible,
    absoluteThresholdProgram_admissible,mainSketchProgram_admissible,
    coarseSupportProgram_admissible,absoluteCoreProgram_admissible,and_self]

end
end HierarchicalAbsoluteSpectral
