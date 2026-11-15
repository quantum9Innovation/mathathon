import HierarchicalAbsoluteSpectral.MainSketchProgram

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix SRHT
open ArithmeticProgram hiding pure

def sketchCoreFormationCap (k m : ℕ) (δ : ℝ) : ℕ :=
  2*2^k+3*embeddingMomentOrder m δ+9+(k+2)*2^k+
    2*m*(k*2^k+k+1+2^k)+3*2^k*m+k+3

def sketchFormationCap (n m : ℕ) (δ : ℝ) : ℕ :=
  2*dyadicPaddingLevel n+1+sketchCoreFormationCap (dyadicPaddingLevel n) m δ

theorem sketchCoreFormationCap_bound (k m : ℕ) (δ : ℝ) :
    sketchCoreFormationCap k m δ ≤ 30*(m+1)*(k+1)*2^k+3*embeddingMomentOrder m δ+20 := by
  have hk : k+1 ≤ 2^k := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
  have hmk := Nat.mul_le_mul_left (2*m) hk
  have hN : 1 ≤ 2^k := Nat.one_le_two_pow
  have hp3 : 0 ≤ m*k*2^k := Nat.zero_le _
  unfold sketchCoreFormationCap
  nlinarith

theorem sketchFormationCap_input_bound (n m : ℕ) (δ : ℝ) (hn : 0 < n) (hm : 1 ≤ m) :
    sketchFormationCap n m δ ≤
      128*m*(dyadicPaddingLevel n+1)*n+3*embeddingMomentOrder m δ+20 := by
  let k := dyadicPaddingLevel n
  have hk : k+1 ≤ 2^k := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
  have hN := (dyadicPaddingLevel_lt_two n hn).le
  have hb := sketchCoreFormationCap_bound k m δ
  have hmul := Nat.mul_le_mul_left (30*(m+1)*(k+1)) hN
  have hn1 : 1 ≤ n := hn
  have hmn : (m+1)*n ≤ 2*m*n := by nlinarith
  have hscale := Nat.mul_le_mul_left (60*(k+1)) hmn
  unfold sketchFormationCap
  change 2*k+1+sketchCoreFormationCap k m δ ≤ _
  nlinarith

theorem boundedSketchCoreProgram_work_le {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) :
    (boundedSketchCoreProgram k hn A ε δ hε hδ g).work ≤ sketchCoreFormationCap k m δ := by
  let M := embeddingComputedRowCount (2^k) m ε δ
  have hMe := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).1
  have hMc := certifiedValue_eq _ _ hMe
  have hcc := certifiedValue_eq _ _ (scalarNatProgram_specification M).1
  have hM : M ≤ 2^k := (embeddingComputedRowCount_specification _ _ _ _ (by positivity) hε).2.1
  have hMp : 0 < M := (embeddingComputedRowCount_specification _ _ _ _ (by positivity) hε).1
  have hparam := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).2.1
  have hsam := gaussianSRHTSampleProgram_work k M hM g
  have hMm := Nat.mul_le_mul_right m hM
  unfold boundedSketchCoreProgram
  simp only [work_bind,certify_work]
  erw [hMc,hcc]
  simp only [(scalarNatProgram_specification M).2.1,ArithmeticProgram.work]
  by_cases hc : (n : ℝ) ≤ (M : ℝ)
  · simp only [dif_pos hc,ArithmeticProgram.work]
    rw [(scalarNatProgram_specification _).2.1]
    unfold sketchCoreFormationCap
    nlinarith
  · simp only [dif_neg hc,work_bind,work_pure,add_zero,embeddingProgram_work]
    rw [(scalarNatProgram_specification _).2.1]
    have hrow := (gaussianSRHTSampleProgram k M hM g).eval.2.2.property
    change (embeddingRowCountProgram (2^k) m ε δ).work+(M+
      (1+((gaussianSRHTSampleProgram k M hM g).work+
        (2*m*(k*2^k+k+1+2^k)+2*2^k*m+k+3+
          (gaussianSRHTSampleProgram k M hM g).eval.2.2.val.card*m)))) ≤ _
    rw [hrow]
    unfold sketchCoreFormationCap
    nlinarith

theorem boundedSketchProgram_work_le {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).work ≤ sketchFormationCap n m δ := by
  have hkc := certifiedValue_eq _ _ (dyadicPaddingProgram_specification n).1
  unfold boundedSketchProgram
  simp only [work_bind,certify_work,(dyadicPaddingProgram_specification n).2.1]
  erw [hkc]
  have hw := boundedSketchCoreProgram_work_le (dyadicPaddingLevel n) (dyadicPaddingLevel_ge n)
    A ε δ hε hδ g
  simpa only [sketchFormationCap,castSketchGaussian] using Nat.add_le_add_left hw (2*dyadicPaddingLevel n+1)

theorem mainSketchProgram_work_le {n m p r L : ℕ} (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (mainSketchProgram I g).work ≤ (L+1)*(sketchFormationCap n m I.sketchFailure+
      sketchFormationCap p m I.sketchFailure) := by
  simp only [mainSketchProgram,work_bind,work_pure,add_zero,finiteTabulateProgram_work]
  have hA : (∑ j : Fin (L+1), (boundedSketchProgram I.A (I.accuracy j.val) I.sketchFailure
      (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I) (mainLeftSketchInput I g j)).work) ≤
      (L+1)*sketchFormationCap n m I.sketchFailure := by
    calc
      _ ≤ ∑ _ : Fin (L+1), sketchFormationCap n m I.sketchFailure :=
        Finset.sum_le_sum (fun _ _ => boundedSketchProgram_work_le _ _ _ _ _ _)
      _ = _ := by simp
  have hB : (∑ j : Fin (L+1), (boundedSketchProgram I.Bᵀ (I.accuracy j.val) I.sketchFailure
      (I.accuracy_positive j.val (by omega)) (mainSketchFailure_positive I) (mainRightSketchInput I g j)).work) ≤
      (L+1)*sketchFormationCap p m I.sketchFailure := by
    calc
      _ ≤ ∑ _ : Fin (L+1), sketchFormationCap p m I.sketchFailure :=
        Finset.sum_le_sum (fun _ _ => boundedSketchProgram_work_le _ _ _ _ _ _)
      _ = _ := by simp
  nlinarith

end
end HierarchicalAbsoluteSpectral
