import HierarchicalAbsoluteSpectral.CorollaryAbsoluteAlgorithm
import HierarchicalAbsoluteSpectral.CorollaryAbsolutePrepared

/-! Gaussian arrays are sampled when their attempt executes. The finite
product tape specifies their joint law, including unused independent
coordinates, and is not itself sampled in full by the algorithm. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

/-- The query uses fresh start and inertia arrays; an accepted query then
uses its fresh carried-filter array. The full-support branch draws none. -/
def absoluteAttemptGaussianDrawCount (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) : ℕ :=
  if hs : s < C.pair.dimension then
    I.repetitions*((s+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+
      if (absolutePositiveQueryProgram kernels I S C s hs t z.1 z.2.1).eval=.below
      then 0 else s*C.pair.dimension
  else 0

theorem absoluteAttemptGaussianDrawCount_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions) :
    absoluteAttemptGaussianDrawCount kernels I S C s t z ≤
      I.repetitions*((s+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s*C.pair.dimension := by
  unfold absoluteAttemptGaussianDrawCount
  split_ifs <;> omega

/-- This follows exactly the executed controller: unused ranks and the
unreached dense fallback contribute no Gaussian samples. -/
def absoluteDoublingGaussianDrawCount
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (draws : ℕ → ℕ) (m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, offset =>
    if m ≤ absoluteRankAt offset then 0 else
      draws (absoluteRankAt offset)+
        match (attempt (absoluteRankAt offset)).eval with
        | some _ => 0
        | none => absoluteDoublingGaussianDrawCount attempt draws m fuel (offset+1)

theorem absoluteDoublingLoop_small_accounted_work
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (draws : ℕ → ℕ)
    (s fuel offset K : ℕ)
    (hstop : ∀ r, s ≤ r → r < m → (attempt r).eval ≠ none)
    (hsmall : 2*s < m)
    (hwork : ∀ r ≤ 2*s, (attempt r).work+draws r ≤ K)
    (hr : absoluteRankAt offset ≤ 2*s)
    (hcap : m ≤ absoluteRankAt (offset+fuel)) :
    (absoluteDoublingLoop attempt fallback fuel offset).work+
      absoluteDoublingGaussianDrawCount attempt draws m fuel offset ≤ fuel*K := by
  induction fuel generalizing offset with
  | zero => simp only [Nat.add_zero] at hcap; omega
  | succ fuel ih =>
    have hm : ¬m ≤ absoluteRankAt offset := by omega
    rw [absoluteDoublingLoop_work_succ,if_neg hm]
    simp only [absoluteDoublingGaussianDrawCount,if_neg hm]
    cases ho : (attempt (absoluteRankAt offset)).eval with
    | some _ =>
      simp only [Nat.add_zero]
      have hw := hwork _ hr
      nlinarith
    | none =>
      have hlt : absoluteRankAt offset < s := by
        by_contra hh
        exact hstop _ (Nat.le_of_not_gt hh) (Nat.lt_of_not_ge hm) ho
      have hw := ih (offset+1) (absoluteRankAt_succ_le hlt)
        (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hcap)
      have ha := hwork _ hr
      nlinarith

theorem absoluteDoublingLoop_accounted_work_cap
    (attempt : ∀ s : ℕ, ArithmeticProgram (Option (FixedRankOutput n p s)))
    (fallback : ArithmeticProgram (FixedRankOutput n p m)) (draws : ℕ → ℕ)
    (fuel offset K : ℕ)
    (hwork : ∀ r < m, (attempt r).work+draws r ≤ K) :
    (absoluteDoublingLoop attempt fallback fuel offset).work+
      absoluteDoublingGaussianDrawCount attempt draws m fuel offset ≤ fuel*K+fallback.work := by
  induction fuel generalizing offset with
  | zero =>
    simp only [absoluteDoublingLoop,absoluteDoublingGaussianDrawCount,work_bind,work_pure,
      Nat.add_zero,Nat.zero_mul,Nat.zero_add]
    exact le_rfl
  | succ fuel ih =>
    rw [absoluteDoublingLoop_work_succ]
    simp only [absoluteDoublingGaussianDrawCount]
    split_ifs with hm
    · omega
    · have ha := hwork _ (Nat.lt_of_not_ge hm)
      cases (attempt (absoluteRankAt offset)).eval with
      | some _ => simp only [Nat.add_zero]; nlinarith
      | none => have hh := ih (offset+1); nlinarith

def absoluteSharedSketchGaussianDrawCount (n p L : ℕ) : ℕ :=
  3*(L+1)*(2^dyadicPaddingLevel n+2^dyadicPaddingLevel p)

def absoluteCoreGaussianDrawCount (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (z : AbsoluteCoreTape I) : ℕ :=
  let t : {t : ℝ // 0 < t} := ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
  let attempt := fun s => if hs : s ≤ m then
    absoluteAttemptProgram kernels I.seed S C s t
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    else .pure none
  let draws := fun s => if hs : s ≤ m then
    absoluteAttemptGaussianDrawCount kernels I.seed S C s t
      (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z ⟨s,by omega⟩))
    else 0
  absoluteDoublingGaussianDrawCount attempt draws m (Nat.log 2 m+2) 0

def absoluteAlgorithmGaussianDrawCount (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ℕ :=
  let S := (mainSketchProgram I.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  absoluteSharedSketchGaussianDrawCount n p L+absoluteCoreGaussianDrawCount kernels I S C g.2

/-- Arithmetic, the Gaussian samples actually requested, and dense output
entries are charged on the same execution. -/
def absoluteRandomizedWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ℕ :=
  (absoluteAlgorithmProgram kernels I g).work+absoluteAlgorithmGaussianDrawCount kernels I g+n*p

def preparedAbsoluteRandomizedWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) : ℕ :=
  (preparedAbsoluteAlgorithmProgram kernels I g).work+absoluteAlgorithmGaussianDrawCount kernels I g+n*p

theorem preparedAbsoluteRandomizedWork_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    preparedAbsoluteRandomizedWork kernels I g=
      4*L+3*I.seed.queryCap+2*I.seed.repetitions+31+absoluteRandomizedWork kernels I g := by
  rw [preparedAbsoluteRandomizedWork,preparedAbsoluteAlgorithmProgram_work]
  unfold absoluteRandomizedWork
  omega

end
end HierarchicalAbsoluteSpectral
