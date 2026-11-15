import HierarchicalAbsoluteSpectral.CorollaryAbsoluteAlgorithm
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteTransfer
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbabilityEvent

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem absoluteAttemptProgram_not_none
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (s : ℕ) (t : {t : ℝ // 0 < t})
    (z : AbsoluteProbabilityTape C.pair.dimension s I.repetitions)
    (hq : ∀ hs : s < C.pair.dimension,
      (absolutePositiveQueryProgram kernels I S C s hs t z.1 z.2.1).eval ≠ .below) :
    (absoluteAttemptProgram kernels I S C s t z).eval ≠ none := by
  unfold absoluteAttemptProgram
  split_ifs with hrank
  · simp only [eval_bind,eval_pure,ne_eq,reduceCtorEq,not_false_eq_true]
  · simp only [eval_bind]
    cases hd : (absolutePositiveQueryProgram kernels I S C s (Nat.lt_of_not_ge hrank) t z.1 z.2.1).eval with
    | below => exact False.elim (hq _ hd)
    | above => simp only [eval_bind,eval_pure,ne_eq,reduceCtorEq,not_false_eq_true]
    | near => simp only [eval_bind,eval_pure,ne_eq,reduceCtorEq,not_false_eq_true]

theorem absoluteCoreProgram_rank_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (z : AbsoluteCoreTape I) :
    (absoluteCoreProgram kernels I S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).eval.attemptRank ≤
      2*I.slackRank := by
  apply absoluteDoublingProgram_rank_bound
  intro s hslack hsm
  rw [dif_pos hsm.le]
  apply absoluteAttemptProgram_not_none
  intro hs
  exact hg.absolute_query_no_false_advance kernels I.seed S C s hs
    ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ _ _
    (hg.absolute_threshold_target_le_one kernels I S C s hs hslack)

/-- The full-support branch and the accepted carried-filter branch both
refer to literal computed outputs. No successful-output hypothesis occurs. -/
theorem absoluteAttemptProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (s : ℕ)
    (z : AbsoluteProbabilityTape C.pair.dimension s I.seed.repetitions)
    (hgood : ∀ hs : s < C.pair.dimension,
      AbsoluteRankThresholdGood kernels I.seed S C s hs (by omega)
        ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z)
    (out : FixedRankOutput n p s)
    (hout : (absoluteAttemptProgram kernels I.seed S C s
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).eval=some out) :
    ‖I.A*I.B-out.product‖ ≤ I.tolerance := by
  unfold absoluteAttemptProgram at hout
  split_ifs at hout with hrank
  · simp only [eval_bind,eval_pure,Option.some.injEq] at hout
    rw [← hout]
    have he := supportExactOutputProgram_exact kernels I.A I.B
      (supportLeftFactor I.A S.initialA C.pair) (supportRightFactor S.initialA C.pair I.B)
      (hg.support_exact I.seed S C) (mainSupportAction kernels I.seed S C _) hrank
    change ‖I.A*I.B-(supportExactOutputProgram kernels I.A I.B
      (mainSupportAction kernels I.seed S C _) hrank).eval.product‖ ≤ I.tolerance
    rw [he,sub_self,norm_zero]
    exact I.tolerance_positive.le
  · have hs : s < C.pair.dimension := Nat.lt_of_not_ge hrank
    simp only [eval_bind] at hout
    cases hd : (absolutePositiveQueryProgram kernels I.seed S C s hs
        ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z.1 z.2.1).eval with
    | below => simp only [hd,eval_pure,reduceCtorEq] at hout
    | above =>
      simp only [hd,eval_bind,eval_pure,Option.some.injEq] at hout
      rw [← hout]
      apply hg.absolute_strong_output_error kernels I S C s (by omega) z.2.2
      apply (hgood hs).2
      rw [hd]
      decide
    | near =>
      simp only [hd,eval_bind,eval_pure,Option.some.injEq] at hout
      rw [← hout]
      apply hg.absolute_strong_output_error kernels I S C s (by omega) z.2.2
      apply (hgood hs).2
      rw [hd]
      decide

theorem absoluteCoreProgram_correct
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (hg : MainSketchGood I.seed S)
    (C : MainSupportData S) (z : AbsoluteCoreTape I)
    (hgood : ∀ s : Fin (m+1), ∀ hs : s.val < C.pair.dimension,
      AbsoluteRankThresholdGood kernels I.seed S C s.val hs (by omega)
        ⟨absoluteThreshold I,absoluteThreshold_positive I⟩
        (absoluteProbabilityTapeRestriction (mainSupport_dimension_le S C) (z s))) :
    let out := (absoluteCoreProgram kernels I S C
      ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).eval
    out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance := by
  dsimp only
  refine ⟨((absoluteCoreProgram kernels I S C
    ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ z).eval.result.width_le).trans
      (absoluteCoreProgram_rank_bound kernels I S hg C z),?_⟩
  apply absoluteDoublingLoop_error
  · intro s out hout
    by_cases hsm : s ≤ m
    · rw [dif_pos hsm] at hout
      exact absoluteAttemptProgram_error kernels I S hg C s _ (hgood ⟨s,by omega⟩) out hout
    · rw [dif_neg hsm,eval_pure] at hout
      contradiction
  · rw [absoluteFullProductProgram_product,sub_self,norm_zero]
    exact I.tolerance_positive.le

theorem absoluteAlgorithmProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (g : AbsoluteTape I) :
    let S := (mainSketchProgram I.seed g.1).eval
    let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
    (absoluteAlgorithmProgram kernels I g).eval =
      (absoluteCoreProgram kernels I S C ⟨absoluteThreshold I,absoluteThreshold_positive I⟩ g.2).eval := by
  have ht : (absoluteThresholdProgram I).certify.eval=
      ⟨absoluteThreshold I,(absoluteThresholdProgram_eval I).symm⟩ :=
    Subtype.ext ((certify_eval _).trans (absoluteThresholdProgram_eval I))
  unfold absoluteAlgorithmProgram
  simp only [eval_bind]
  erw [ht]

end
end HierarchicalAbsoluteSpectral
