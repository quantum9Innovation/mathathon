import HierarchicalAbsoluteSpectral.CorollaryAbsoluteRuntime

/-! An intermediate cost envelope for all attempted ranks, including zero.
It is discharged by the actual family action, degree and kernel bounds;
none of its fields is a successful-output or complete-runtime assumption. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {n m p r L : ℕ}

structure AbsoluteAttemptEnvelope (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ) : Prop where
  action_positive : 1 ≤ A
  core_positive : 1 ≤ B
  output_positive : 1 ≤ O
  factor : ∀ b ≤ R+1, mainFactorActionCost kernels I S C b L ≤ A
  true_action : ∀ b ≤ R+1, mainTrueActionCost kernels I S C b ≤ A
  core_kernel : ∀ b ≤ R+1, (kernels C.pair.dimension C.pair.dimension b).cost ≤ A
  block_entries : C.pair.dimension*(R+1) ≤ A
  base : baseConstructionCost kernels C.pair.dimension (I.accuracy 0)
    (I.accuracy_positive 0 (by omega)) ≤ B
  core_envelope : kernelEnvelope kernels C.pair.dimension ≤ B
  square_entries : C.pair.dimension*C.pair.dimension ≤ B
  physical_range : ∀ s ≤ R, exactRangeWorkCap kernels n s ≤ O
  projection : ∀ s ≤ R, projectionOutputWorkCap kernels n m p s ≤ O
  physical_kernel : ∀ s ≤ R, (kernels n m s).cost ≤ A
  support_kernel : ∀ s ≤ R, (kernels m C.pair.dimension s).cost ≤ A
  query_degree : ∀ s ≤ R, ∀ hs : s < C.pair.dimension, absoluteQueryDegree I S C hs ≤ Q
  query_range : ∀ s ≤ R, ∀ hs : s < C.pair.dimension, absoluteQueryRangeCap kernels I S C hs ≤ B
  test : ⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊ ≤ B
  strong_degree : ∀ hk : 1 ≤ C.pair.dimension, absoluteStrongDegree I S C hk ≤ Q

theorem AbsoluteAttemptEnvelope.threshold_action
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q) (s : ℕ) (hs : s ≤ R) :
    mainThresholdActionCost kernels I S C (s+1) ≤ 4*A := by
  have hf := h.factor (s+1) (by omega)
  have ht := h.true_action (s+1) (by omega)
  have hb : C.pair.dimension*(s+1) ≤ A :=
    (Nat.mul_le_mul_left _ (by omega : s+1 ≤ R+1)).trans h.block_entries
  unfold mainThresholdActionCost
  omega

theorem AbsoluteAttemptEnvelope.carried_action
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q) (s : ℕ) (hs : s ≤ R) :
    mainCarriedActionCost kernels I S C s ≤ 6*A := by
  have hf := h.factor s (by omega)
  have ht := h.true_action s (by omega)
  have hk := h.core_kernel s (by omega)
  have hb : C.pair.dimension*s ≤ A :=
    (Nat.mul_le_mul_left _ (by omega : s ≤ R+1)).trans h.block_entries
  unfold mainCarriedActionCost
  omega

theorem AbsoluteAttemptEnvelope.query_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q)
    (s : ℕ) (hs : s ≤ R) (hr : s < C.pair.dimension) :
    absoluteQueryWorkCap kernels I S C hr Ck p0 ≤ 40*(I.repetitions+1)*((Q+1)*A+B) := by
  have hf := h.factor (s+1) (by omega)
  have hk := h.core_kernel (s+1) (by omega)
  have ht := h.threshold_action kernels I S C Ck p0 R A B O Q s hs
  have hq := h.query_degree s hs hr
  have hrange := h.query_range s hs hr
  have htrial : absoluteQueryTrialCap kernels I S C hr Ck p0 ≤ 12*(Q+1)*A+5*B := by
    unfold absoluteQueryTrialCap
    calc
      _ ≤ A+A+(3*Q+2)*(4*A)+B+3*B+B := by
        gcongr <;> first | assumption | exact h.core_envelope | exact h.test
      _ = 12*Q*A+10*A+5*B := by ring
      _ ≤ _ := by nlinarith
  have hQA : Q ≤ (Q+1)*A := by nlinarith [Nat.mul_le_mul_left (Q+1) h.action_positive]
  have hbase : B+2*B+8+4*Q+15 ≤ 30*((Q+1)*A+B) := by
    have := h.core_positive
    nlinarith
  have htrial' : 12*(Q+1)*A+5*B ≤ 12*((Q+1)*A+B) := by nlinarith
  simp only [absoluteQueryWorkCap,Nat.mul_assoc]
  calc
    _ ≤ B+2*B+8+4*Q+15+I.repetitions*(12*(Q+1)*A+5*B) := by
      gcongr <;> first | assumption | exact h.base | exact h.square_entries
    _ ≤ 30*((Q+1)*A+B)+I.repetitions*(12*((Q+1)*A+B)) :=
      Nat.add_le_add hbase (Nat.mul_le_mul_left _ htrial')
    _ ≤ _ := by nlinarith

theorem AbsoluteAttemptEnvelope.strong_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q)
    (s : ℕ) (hs : s ≤ R) (hk : 1 ≤ C.pair.dimension) :
    absoluteStrongWorkCap kernels I S C s hk ≤ 50*((Q+1)*A+B+O) := by
  have hv := h.strong_degree hk
  have hc := h.carried_action kernels I S C Ck p0 R A B O Q s hs
  have hkr : C.pair.dimension*s ≤ A :=
    (Nat.mul_le_mul_left _ (by omega : s ≤ R+1)).trans h.block_entries
  have hkernel := h.core_kernel s (by omega)
  have hQA : Q ≤ (Q+1)*A := by nlinarith [Nat.mul_le_mul_left (Q+1) h.action_positive]
  have hA : A ≤ (Q+1)*A := by nlinarith
  dsimp only [absoluteStrongWorkCap,absoluteStrongOutputCap]
  simp only [Nat.mul_assoc]
  calc
    _ ≤ B+2*B+7+(4*Q+14+(9+3*Q+(Q+1)*(6*A+6*A)+A+A+A+A+O)+O) := by
      gcongr <;> first | assumption | exact h.base | exact h.square_entries |
        exact h.physical_range s hs | exact h.projection s hs |
        exact h.physical_kernel s hs | exact h.support_kernel s hs
    _ ≤ _ := by have := h.core_positive; nlinarith

theorem AbsoluteAttemptEnvelope.exact_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q)
    (s : ℕ) (hs : s ≤ R) (hk : C.pair.dimension ≤ s) :
    absoluteExactWorkCap kernels I S C s ≤ 2*A+2*O := by
  have hsize : C.pair.dimension ≤ R := hk.trans hs
  have h1 := h.physical_kernel _ hsize
  have h2 := h.support_kernel _ hsize
  have h3 := h.physical_range _ hsize
  have h4 := h.projection s hs
  unfold absoluteExactWorkCap
  omega

theorem AbsoluteAttemptEnvelope.attempt_work_with_draws
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I S C Ck p0 R A B O Q) (s : ℕ) (hs : s ≤ R) :
    absoluteAttemptWorkCap kernels I S C s Ck p0+
      I.repetitions*((s+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s*C.pair.dimension ≤
        1000*(I.repetitions+1)*((Q+1)*A+B+O) := by
  have hb : (s+1)*C.pair.dimension ≤ A := by
    simpa only [Nat.mul_comm] using
      (Nat.mul_le_mul_left C.pair.dimension (by omega : s+1 ≤ R+1)).trans h.block_entries
  have hbs : s*C.pair.dimension ≤ A :=
    (Nat.mul_le_mul_right _ (by omega : s ≤ s+1)).trans hb
  have hkk : 2*C.pair.dimension*C.pair.dimension ≤ 2*B := by nlinarith [h.square_entries]
  have hd : I.repetitions*((s+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s*C.pair.dimension ≤
      I.repetitions*(A+2*B)+A :=
    Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add hb hkk)) hbs
  have hQA : A ≤ (Q+1)*A := by nlinarith
  by_cases hr : s < C.pair.dimension
  · have hq := h.query_work kernels I S C Ck p0 R A B O Q s hs hr
    have hf := h.strong_work kernels I S C Ck p0 R A B O Q s hs (by omega)
    rw [absoluteAttemptWorkCap,dif_pos hr]
    nlinarith only [hq,hf,hd,hQA]
  · have he := h.exact_work kernels I S C Ck p0 R A B O Q s hs (Nat.le_of_not_gt hr)
    rw [absoluteAttemptWorkCap,dif_neg hr]
    nlinarith only [he,hd,hQA]

theorem AbsoluteAttemptEnvelope.uniform_work_with_draws
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (R A B O Q : ℕ)
    (h : AbsoluteAttemptEnvelope kernels I.seed S C Ck p0 R A B O Q) :
    absoluteUniformAttemptWorkCap kernels I S C R Ck p0 ≤
      1000*(I.seed.repetitions+1)*((Q+1)*A+B+O) := by
  apply Finset.sup_le
  intro s hs
  exact h.attempt_work_with_draws kernels I.seed S C Ck p0 R A B O Q s.val (by omega)

end
end HierarchicalAbsoluteSpectral
