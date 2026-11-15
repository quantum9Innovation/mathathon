import HierarchicalAbsoluteSpectral.BaseFixedCoreAlgebraCost
import HierarchicalAbsoluteSpectral.BaseMainFlexibleQueryCost

/-! Coarse-base setup is a separate additive term in the actual main query
and strong-filter programs.  The trial/output caps retain their original
locations, so these estimates introduce no degree times core-algebra term. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L : ℕ}
attribute [local irreducible] mainPositiveQueryProgram mainStrongThresholdProgram

def baseFixedInitialLog (I : FixedProblem n m p r L) : ℝ :=
  1+4*Real.log (1/(4*I.accuracy 0))

theorem baseFixedInitialLog_ge_one (I : FixedProblem n m p r L) : 1 ≤ baseFixedInitialLog I := by
  have hh := I.accuracy_positive 0 (by omega)
  have harg : 1 ≤ 1/(4*I.accuracy 0) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*I.accuracy 0)).mpr
    linarith [I.initial_accuracy_le]
  have hlog := Real.log_nonneg harg
  unfold baseFixedInitialLog
  linarith

theorem mainBaseSetupCost_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S) (d : ℕ) :
    ((baseConstructionCost K D.pair.dimension (I.accuracy 0) (I.accuracy_positive 0 (by omega))+
      2*D.pair.dimension*D.pair.dimension+d:ℕ):ℝ) ≤
      (36+(d:ℝ))*(C+1)*(m:ℝ)^e*baseFixedInitialLog I :=
  baseFixedSetupCost_log_bound K C e hC he hK D.pair.dimension m d
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)
    (mainSupport_dimension_le S D) (I.accuracy 0) (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le

theorem mainCoarseSupportProgram_work_core_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) :
    ((coarseSupportProgram K S.initialA S.initialB).work:ℝ) ≤
      baseFixedCoarseGramCost K m (S.levelA 0).1 (S.levelB 0).1+11*(C+1)*(m:ℝ)^e :=
  coarseSupportProgram_work_core_bound K C e hC he hK S.initialA S.initialB
    (by have hh:=I.rank_positive; have hh':=I.rank_le_core; omega)

theorem mainQueryWorkCap_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hr : r < D.pair.dimension) :
    (mainQueryWorkCap K I S D hr C e:ℝ) ≤
      44*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+4*(mainQueryDegree I S D hr:ℝ)+15+
        (I.repetitions:ℝ)*mainQueryTrialCap K I S D hr C e := by
  have hb := mainBaseSetupCost_core_bound K C e hC he hK I S D 8
  unfold mainQueryWorkCap
  push_cast at hb ⊢
  linarith

theorem mainPositiveQueryProgram_work_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hr : r < D.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin D.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (D.pair.dimension*D.pair.dimension) → ℝ) :
    ((mainPositiveQueryProgram K I S D hr t G g).work:ℝ) ≤
      44*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+4*(mainQueryDegree I S D hr:ℝ)+15+
        (I.repetitions:ℝ)*mainQueryTrialCap K I S D hr C e :=
  (Nat.cast_le.mpr (mainPositiveQueryProgram_work_bound K C e hC he hK I S D hr t G g)).trans
    (mainQueryWorkCap_core_setup_bound K C e hC he hK I S D hr)

theorem mainFlexibleQueryWorkCap_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hr : r < D.pair.dimension) :
    (mainFlexibleQueryWorkCap K R I S D hr C e:ℝ) ≤
      44*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+4*(mainQueryDegree I S D hr:ℝ)+15+
        (I.repetitions:ℝ)*mainFlexibleQueryTrialCap K R I S D hr C e := by
  have hb := mainBaseSetupCost_core_bound K C e hC he hK I S D 8
  unfold mainFlexibleQueryWorkCap
  push_cast at hb ⊢
  linarith

theorem mainPositiveQueryProgram_work_flexible_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a →
      (orthogonalRangeProgram K Y).work ≤ R a b)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hr : r < D.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin D.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (D.pair.dimension*D.pair.dimension) → ℝ) :
    ((mainPositiveQueryProgram K I S D hr t G g).work:ℝ) ≤
      44*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+4*(mainQueryDegree I S D hr:ℝ)+15+
        (I.repetitions:ℝ)*mainFlexibleQueryTrialCap K R I S D hr C e :=
  (Nat.cast_le.mpr (mainPositiveQueryProgram_work_bound_flexible K R hR C e hC he hK I S D hr t G g)).trans
    (mainFlexibleQueryWorkCap_core_setup_bound K C e hC he hK R I S D hr)

theorem mainStrongWorkCap_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hk : 1 ≤ D.pair.dimension) :
    (mainStrongWorkCap K I S D hk:ℝ) ≤
      43*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+mainStrongOutputCap K I S D hk := by
  have hb := mainBaseSetupCost_core_bound K C e hC he hK I S D 7
  unfold mainStrongWorkCap
  push_cast at hb ⊢
  linarith

theorem mainStrongThresholdProgram_work_core_setup_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C e : ℝ) (hC : 0 < C) (he : 2 ≤ e)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ C*(N:ℝ)^e)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (D : MainSupportData S)
    (hk : 1 ≤ D.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin D.pair.dimension → ℝ) :
    ((mainStrongThresholdProgram K I S D hk t G).work:ℝ) ≤
      43*(C+1)*(m:ℝ)^e*baseFixedInitialLog I+mainStrongOutputCap K I S D hk :=
  (Nat.cast_le.mpr (mainStrongThresholdProgram_work_bound K I S D hk t G)).trans
    (mainStrongWorkCap_core_setup_bound K C e hC he hK I S D hk)

end
end HierarchicalAbsoluteSpectral
