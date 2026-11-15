import HierarchicalAbsoluteSpectral.BaseMainCoreCost

/-! Algebraic unfolding of the actual finite core cap.  Krylov degree
multiplies only the block-action charge, while range, inertia and dense
output charges remain additive.  This distinction is needed for the
optimized comparator exponent. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
variable {n m p r L : ℕ}

/-- An intermediate arithmetic envelope, subsequently discharged from
verified circuit, scalar-degree and dimension estimates. -/
structure ComparatorCoreEnvelope (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) : Prop where
  action_positive : 1 ≤ A
  core_positive : 1 ≤ B
  output_positive : 1 ≤ O
  factor : ∀ b ≤ r+1, mainFactorActionCost kernels I S C b L ≤ A
  true_action : ∀ b ≤ r+1, mainTrueActionCost kernels I S C b ≤ A
  core_kernel : ∀ b ≤ r+1, (kernels C.pair.dimension C.pair.dimension b).cost ≤ A
  block_entries : C.pair.dimension*(r+1) ≤ A
  base : baseConstructionCost kernels C.pair.dimension (I.accuracy 0)
    (I.accuracy_positive 0 (by omega)) ≤ B
  core_envelope : kernelEnvelope kernels C.pair.dimension ≤ B
  psd : psdGramCost kernels r ≤ B
  square_entries : C.pair.dimension*C.pair.dimension ≤ B
  dimension : C.pair.dimension ≤ B
  exact_output : mainExactOutputWorkCap kernels I S C ≤ O
  physical_range : exactRangeWorkCap kernels n r ≤ O
  projection : projectionOutputWorkCap kernels n m p r ≤ O
  physical_kernel : (kernels n m r).cost ≤ A
  support_kernel : (kernels m C.pair.dimension r).cost ≤ A
  query_degree : ∀ hr : r < C.pair.dimension, mainQueryDegree I S C hr ≤ Q
  query_range : ∀ hr : r < C.pair.dimension, mainQueryRangeCap kernels I S C hr ≤ B
  test : ⌈212*(Ck+1)*(C.pair.dimension:ℝ)^p0⌉₊ ≤ B
  strong_degree : ∀ hk : 1 ≤ C.pair.dimension, mainStrongDegree I S C hk ≤ Q

theorem ComparatorCoreEnvelope.threshold_action
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) (h : ComparatorCoreEnvelope kernels I S C Ck p0 A B O Q) :
    mainThresholdActionCost kernels I S C (r+1) ≤ 4*A := by
  have hf := h.factor (r+1) le_rfl
  have ht := h.true_action (r+1) le_rfl
  have hb := h.block_entries
  unfold mainThresholdActionCost
  omega

theorem ComparatorCoreEnvelope.carried_action
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) (h : ComparatorCoreEnvelope kernels I S C Ck p0 A B O Q) :
    mainCarriedActionCost kernels I S C r ≤ 6*A := by
  have hf := h.factor r (by omega)
  have ht := h.true_action r (by omega)
  have hk := h.core_kernel r (by omega)
  have hb : C.pair.dimension*r ≤ A :=
    (Nat.mul_le_mul_left _ (by omega : r ≤ r+1)).trans h.block_entries
  unfold mainCarriedActionCost
  omega

theorem ComparatorCoreEnvelope.query_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) (h : ComparatorCoreEnvelope kernels I S C Ck p0 A B O Q)
    (hr : r < C.pair.dimension) :
    mainQueryWorkCap kernels I S C hr Ck p0 ≤
      40*(I.repetitions+1)*((Q+1)*A+B) := by
  have hf := h.factor (r+1) le_rfl
  have hk := h.core_kernel (r+1) le_rfl
  have ht := ComparatorCoreEnvelope.threshold_action kernels I S C Ck p0 A B O Q h
  have hq := h.query_degree hr
  have hrange := h.query_range hr
  have htrial : mainQueryTrialCap kernels I S C hr Ck p0 ≤ 12*(Q+1)*A+5*B := by
    unfold mainQueryTrialCap
    calc
      _ ≤ A+A+(3*Q+2)*(4*A)+B+3*B+B := by gcongr <;> first | assumption | exact h.core_envelope | exact h.test
      _ = 12*Q*A+10*A+5*B := by ring
      _ ≤ _ := by nlinarith
  have hQA : Q ≤ (Q+1)*A := by nlinarith [Nat.mul_le_mul_left (Q+1) h.action_positive]
  have hbase : B+2*B+8+4*Q+15 ≤ 30*((Q+1)*A+B) := by
    have := h.core_positive
    nlinarith
  have htrial' : 12*(Q+1)*A+5*B ≤ 12*((Q+1)*A+B) := by nlinarith
  simp only [mainQueryWorkCap,Nat.mul_assoc]
  calc
    _ ≤ B+2*B+8+4*Q+15+I.repetitions*(12*(Q+1)*A+5*B) := by
      gcongr <;> first | assumption | exact h.base | exact h.square_entries
    _ ≤ 30*((Q+1)*A+B)+I.repetitions*(12*((Q+1)*A+B)) :=
      Nat.add_le_add hbase (Nat.mul_le_mul_left _ htrial')
    _ ≤ _ := by nlinarith

theorem ComparatorCoreEnvelope.strong_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) (h : ComparatorCoreEnvelope kernels I S C Ck p0 A B O Q)
    (hk : 1 ≤ C.pair.dimension) :
    mainStrongWorkCap kernels I S C hk ≤ 50*((Q+1)*A+B+O) := by
  have hv := h.strong_degree hk
  have hc := ComparatorCoreEnvelope.carried_action kernels I S C Ck p0 A B O Q h
  have hkr : C.pair.dimension*r ≤ A :=
    (Nat.mul_le_mul_left _ (by omega : r ≤ r+1)).trans h.block_entries
  have hkernel := h.core_kernel r (by omega)
  have hQA : Q ≤ (Q+1)*A := by nlinarith [Nat.mul_le_mul_left (Q+1) h.action_positive]
  have hA : A ≤ (Q+1)*A := by nlinarith
  dsimp only [mainStrongWorkCap,mainStrongOutputCap]
  simp only [Nat.mul_assoc]
  calc
    _ ≤ B+2*B+7+(4*Q+14+(9+3*Q+(Q+1)*(6*A+6*A)+
        A+A+A+A+O)+O) := by
      gcongr <;> first | assumption | exact h.base | exact h.square_entries |
        exact h.physical_range | exact h.projection | exact h.physical_kernel | exact h.support_kernel
    _ ≤ _ := by have := h.core_positive; nlinarith

/-- The literal cap has an additive range/output term: the outer degree
does not multiply a full small-core factorization or dense output. -/
theorem ComparatorCoreEnvelope.core_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck p0 : ℝ) (A B O Q : ℕ) (h : ComparatorCoreEnvelope kernels I S C Ck p0 A B O Q) :
    mainCoreWorkCap kernels I S C Ck p0 ≤
      1000*(I.queryCap+1)*(I.repetitions+1)*((Q+1)*A+B+O) := by
  have hW : 1 ≤ (Q+1)*A+B+O := by have := h.core_positive; omega
  by_cases hr : C.pair.dimension ≤ r
  · simp only [mainCoreWorkCap,dif_pos hr]
    apply h.exact_output.trans
    have h1 : O ≤ (Q+1)*A+B+O := by omega
    have h2 : 0 < 1000*(I.queryCap+1)*(I.repetitions+1) := by positivity
    nlinarith
  · have hrl : r < C.pair.dimension := Nat.lt_of_not_ge hr
    have hk : 1 ≤ C.pair.dimension := by omega
    have hq := ComparatorCoreEnvelope.query_work kernels I S C Ck p0 A B O Q h hrl
    have hs := ComparatorCoreEnvelope.strong_work kernels I S C Ck p0 A B O Q h hk
    have hi : 5*kernelEnvelope kernels C.pair.dimension+psdGramCost kernels r+
        3*C.pair.dimension*C.pair.dimension+C.pair.dimension+10 ≤ 20*B := by
      have := h.core_envelope
      have := h.psd
      have := h.square_entries
      have := h.dimension
      have := h.core_positive
      nlinarith
    have hq' : mainQueryWorkCap kernels I S C hrl Ck p0 ≤
        40*(I.repetitions+1)*((Q+1)*A+B+O) := by
      exact hq.trans (Nat.mul_le_mul_left _ (by omega))
    simp only [mainCoreWorkCap,dif_neg hr,mainBracketWorkCap]
    calc
      _ ≤ 20*B+O+(12+I.queryCap*(8+40*(I.repetitions+1)*((Q+1)*A+B+O))+
          50*((Q+1)*A+B+O)) := by gcongr <;> first | assumption | exact h.exact_output
      _ ≤ _ := by
        have hrep : 1 ≤ I.repetitions+1 := by omega
        have hBW : B ≤ (Q+1)*A+B+O := by omega
        have hOW : O ≤ (Q+1)*A+B+O := by omega
        have hrepW := Nat.mul_le_mul_right ((Q+1)*A+B+O) hrep
        have hcapW := Nat.mul_le_mul_left I.queryCap hrepW
        nlinarith

end
end HierarchicalAbsoluteSpectral
