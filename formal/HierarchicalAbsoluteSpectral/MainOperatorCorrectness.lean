import HierarchicalAbsoluteSpectral.MainOperatorProgram
import HierarchicalAbsoluteSpectral.MainSketchGood

/-! The original simultaneous sketch event implies the full finite
hierarchy for the actual operator constructor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {n m p r L : ℕ}

theorem FixedProblem.accuracy_succ_le (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j < L) : I.accuracy (j+1) ≤ I.accuracy j := by
  have hp := I.accuracy_positive j (by omega)
  have hh := (div_le_iff₀ hp).mp (I.refinement_ratio j hj)
  linarith

theorem FixedProblem.accuracy_antitone (I : FixedProblem n m p r L)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ L) : I.accuracy j ≤ I.accuracy i := by
  induction hij with
  | refl => exact le_rfl
  | @step j hij ih =>
      exact (I.accuracy_succ_le j (by omega)).trans (ih (by omega))

theorem FixedProblem.accuracy_bounded (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j ≤ L) : I.accuracy j ≤ 1/64 :=
  (I.accuracy_antitone 0 j (Nat.zero_le _) hj).trans I.initial_accuracy_le

theorem FixedProblem.massAccuracy_le_level (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j ≤ L) : I.massAccuracy ≤ I.accuracy j/100 :=
  I.final_budget.mass_floor.trans (div_le_div_of_nonneg_right
    (I.accuracy_antitone j L hj le_rfl) (by norm_num))

theorem safeAccuracy_eq (I : FixedProblem n m p r L) (j : ℕ) (hj : j ≤ L) :
    safeAccuracy I j = I.accuracy j := by simp [safeAccuracy, min_eq_left hj]

theorem mainTrueGram_eq (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : mainTrueGram I S C =
      (supportLeftFactor I.A S.initialA C.pair)ᵀ*supportLeftFactor I.A S.initialA C.pair := by
  simp only [mainTrueGram, supportLeftFactor, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mainTrueRightGram_eq (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) : mainTrueRightGram I S C =
      supportRightFactor S.initialA C.pair I.B*(supportRightFactor S.initialA C.pair I.B)ᵀ := by
  simp only [mainTrueRightGram, supportRightFactor, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mainTrueRightGram_posSemidef (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) :
    (mainTrueRightGram I S C).PosSemidef := by
  have hh := Matrix.posSemidef_conjTranspose_mul_self (I.Bᵀ*C.pair.factor)
  simpa only [mainTrueRightGram, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using hh

theorem mainFineRightGram_zero (S : StoredSketches n m p L) (C : MainSupportData S) :
    mainFineRightGram S C 0 = C.rightGram := by
  have hi : safeSketchIndex L 0 = 0 := by
    apply Fin.ext
    exact Nat.zero_min L
  rw [mainFineRightGram, hi]
  exact C.rightGram_eq.symm

theorem MainSketchGood.support_exact (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    I.A*I.B=supportLeftFactor I.A S.initialA C.pair*supportRightFactor S.initialA C.pair I.B := by
  apply C.support_exact I.A I.B (I.accuracy 0) (by linarith [I.initial_accuracy_le])
  exact (hg 0).1.1

theorem MainSketchGood.normalized_gram_bounds (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    (1/(1+I.accuracy 0)) • (1 : Core C.pair.dimension) ≤ mainTrueGram I S C ∧
      mainTrueGram I S C ≤ (1/(1-I.accuracy 0)) • (1 : Core C.pair.dimension) := by
  rw [mainTrueGram_eq]
  exact support_normalized_gram I.A S.initialA C.pair (I.accuracy 0)
    (I.accuracy_positive 0 (by omega)).le (by linarith [I.initial_accuracy_le])
    (hg 0).1.1 (hg 0).1.2

theorem MainSketchGood.fine_gram_bounds (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S)
    (j : ℕ) (hj : j ≤ L) :
    (1-I.accuracy j) • mainTrueGram I S C ≤ mainFineGram S C j ∧
      mainFineGram S C j ≤ (1+I.accuracy j) • mainTrueGram I S C := by
  have hh := (hg ⟨j,by omega⟩).1
  have hl := support_gram_congruence_mono hh.1 C.pair.leftInverseᵀ
  have hu := support_gram_congruence_mono hh.2 C.pair.leftInverseᵀ
  simpa only [mainFineGram, safeSketchIndex, min_eq_left hj, mainTrueGram,
    Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul] using And.intro hl hu

theorem MainSketchGood.fine_right_bounds (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S)
    (j : ℕ) (hj : j ≤ L) :
    (1-I.accuracy j) • mainTrueRightGram I S C ≤ mainFineRightGram S C j ∧
      mainFineRightGram S C j ≤ (1+I.accuracy j) • mainTrueRightGram I S C := by
  have hh := (hg ⟨j,by omega⟩).2
  have hl := support_gram_congruence_mono hh.1 C.pair.factor
  have hu := support_gram_congruence_mono hh.2 C.pair.factor
  simpa only [SketchGramApprox, mainFineRightGram, safeSketchIndex, min_eq_left hj,
    mainTrueRightGram, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul] using And.intro hl hu

theorem normalized_sketch_scalar_bands (h₀ h : ℝ)
    (h₀pos : 0 ≤ h₀) (h₀max : h₀ ≤ 1/64) (hpos : 0 ≤ h) (hmax : h ≤ 1/64) :
    (1/2 : ℝ) ≤ (1-h)/(1+h₀) ∧ (1+h)/(1-h₀) ≤ (3/2 : ℝ) := by
  constructor
  · apply (le_div_iff₀ (by linarith : 0 < 1+h₀)).mpr
    linarith
  · apply (div_le_iff₀ (by linarith : 0 < 1-h₀)).mpr
    linarith

theorem MainSketchGood.gram_bands (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    (1/2 : ℝ) • (1 : Core C.pair.dimension) ≤ mainTrueGram I S C ∧
      mainTrueGram I S C ≤ (3/2 : ℝ) • (1 : Core C.pair.dimension) := by
  have hh := hg.normalized_gram_bounds I S C
  have hs := normalized_sketch_scalar_bands (I.accuracy 0) 0
    (I.accuracy_positive 0 (by omega)).le I.initial_accuracy_le (by norm_num) (by norm_num)
  simp only [sub_zero, add_zero] at hs
  exact ⟨(smul_le_smul_of_nonneg_right hs.1 Matrix.PosSemidef.one.nonneg).trans hh.1,
    hh.2.trans (smul_le_smul_of_nonneg_right hs.2 Matrix.PosSemidef.one.nonneg)⟩

theorem MainSketchGood.fine_gram_bands (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S)
    (j : ℕ) (hj : j ≤ L) :
    (1/2 : ℝ) • (1 : Core C.pair.dimension) ≤ mainFineGram S C j ∧
      mainFineGram S C j ≤ (3/2 : ℝ) • (1 : Core C.pair.dimension) := by
  have hbase := hg.normalized_gram_bounds I S C
  have hfine := hg.fine_gram_bounds I S C j hj
  have hpos := I.accuracy_positive j hj
  have hmax := I.accuracy_bounded j hj
  have hs := normalized_sketch_scalar_bands (I.accuracy 0) (I.accuracy j)
    (I.accuracy_positive 0 (by omega)).le I.initial_accuracy_le hpos.le hmax
  have hl := smul_le_smul_of_nonneg_left hbase.1 (by linarith : 0 ≤ 1-I.accuracy j)
  have hu := smul_le_smul_of_nonneg_left hbase.2 (by linarith : 0 ≤ 1+I.accuracy j)
  rw [smul_smul] at hl hu
  constructor
  · have hs' : (1/2 : ℝ) ≤ (1-I.accuracy j)*(1/(1+I.accuracy 0)) := by
      simpa only [div_eq_mul_inv, one_mul] using hs.1
    exact (smul_le_smul_of_nonneg_right hs' Matrix.PosSemidef.one.nonneg).trans (hl.trans hfine.1)
  · have hs' : (1+I.accuracy j)*(1/(1-I.accuracy 0)) ≤ (3/2 : ℝ) := by
      simpa only [div_eq_mul_inv, one_mul] using hs.2
    exact (hfine.2.trans hu).trans (smul_le_smul_of_nonneg_right hs' Matrix.PosSemidef.one.nonneg)

theorem MainSketchGood.coarse_right_bounds (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    (1-I.accuracy 0) • mainTrueRightGram I S C ≤ C.rightGram ∧
      C.rightGram ≤ (1+I.accuracy 0) • mainTrueRightGram I S C := by
  simpa only [mainFineRightGram_zero] using hg.fine_right_bounds I S C 0 (by omega)

theorem MainSketchGood.right_gram_comparison (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (hg : MainSketchGood I S) (C : MainSupportData S) :
    mainTrueRightGram I S C ≤ (2 : ℝ) • C.rightGram ∧
      C.rightGram ≤ (2 : ℝ) • mainTrueRightGram I S C := by
  have hh := hg.coarse_right_bounds I S C
  have hmax := I.initial_accuracy_le
  have hpos := I.accuracy_positive 0 (by omega)
  have hinv : 0 < 1-I.accuracy 0 := by linarith
  have hi : 1/(1-I.accuracy 0) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hinv).mpr
    linarith
  constructor
  · have hl := smul_le_smul_of_nonneg_left hh.1 (by positivity : 0 ≤ 1/(1-I.accuracy 0))
    have he : (1/(1-I.accuracy 0))*(1-I.accuracy 0) = 1 := by field_simp
    rw [smul_smul, he, one_smul] at hl
    exact hl.trans (smul_le_smul_of_nonneg_right hi C.rightGram_posSemidef.nonneg)
  · exact hh.2.trans (smul_le_smul_of_nonneg_right
      (show 1+I.accuracy 0 ≤ (2 : ℝ) by linarith) (mainTrueRightGram_posSemidef I S C).nonneg)

theorem MainSketchGood.fine_pencil_error (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 ≤ t) (j : ℕ) (hj : j < L) :
    -((8*safeAccuracy I (j+1)) • (t • (1 : Core C.pair.dimension)+C.rightGram)) ≤
      mainFinePencil I S C t j-mainTruePencil I S C t ∧
      mainFinePencil I S C t j-mainTruePencil I S C t ≤
        (8*safeAccuracy I (j+1)) • (t • (1 : Core C.pair.dimension)+C.rightGram) := by
  have hb := hg.gram_bands I S C
  have hf := hg.fine_gram_bands I S C (j+1) (by omega)
  have hfg := hg.fine_gram_bounds I S C (j+1) (by omega)
  have hq := hg.fine_right_bounds I S C (j+1) (by omega)
  have ha := safeAccuracy_eq I (j+1) (by omega)
  have hmax : safeAccuracy I (j+1) ≤ 1/64 := by
    rw [ha]
    exact I.accuracy_bounded (j+1) (by omega)
  have hmass : I.massAccuracy ≤ safeAccuracy I (j+1)/100 := by
    rw [ha]
    exact I.massAccuracy_le_level (j+1) (by omega)
  have hfglo : (1-safeAccuracy I (j+1)) • mainTrueGram I S C ≤ mainFineGram S C (j+1) := by
    rw [ha]
    exact hfg.1
  have hfgup : mainFineGram S C (j+1) ≤ (1+safeAccuracy I (j+1)) • mainTrueGram I S C := by
    rw [ha]
    exact hfg.2
  have hqlo : (1-safeAccuracy I (j+1)) • mainTrueRightGram I S C ≤ mainFineRightGram S C (j+1) := by
    rw [ha]
    exact hq.1
  have hqup : mainFineRightGram S C (j+1) ≤ (1+safeAccuracy I (j+1)) • mainTrueRightGram I S C := by
    rw [ha]
    exact hq.2
  exact constructed_fine_pencil_error (k := C.pair.dimension) (mainTrueGram I S C) (mainFineGram S C (j+1))
      (mainTrueRightGram I S C) (mainFineRightGram S C (j+1)) C.rightGram
      (safeAccuracy I (j+1)) t I.massAccuracy (safeAccuracy_pos I (j+1))
      hmax I.final_budget.mass_positive hmass ht C.rightGram_posSemidef
      hb.1 hb.2 hf.1 hf.2 hfglo hfgup (hg.right_gram_comparison I S C).1 hqlo hqup

theorem MainSketchGood.actual_hierarchy (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (t : ℝ) (ht : 0 < t) :
    let base := (coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t ht
      (I.accuracy 0) (I.accuracy_positive 0 (by omega))).eval
    HierarchyInvariant (mainRefinedFactor I S C t base) (mainTruePencil I S C t)
      (t • (1 : Core C.pair.dimension)+C.rightGram) L (I.accuracy L) := by
  have hD : (t • (1 : Core C.pair.dimension)+C.rightGram).PosDef :=
    (Matrix.PosDef.one.smul ht).add_posSemidef C.rightGram_posSemidef
  have hG := hg.normalized_gram_bounds I S C
  have hQ := hg.coarse_right_bounds I S C
  have hbase := base_hierarchy_invariant kernels (mainTrueGram I S C) (mainTrueRightGram I S C)
    C.rightGram (mainTrueRightGram_posSemidef I S C) C.rightGram_posSemidef
    (I.accuracy 0) I.massAccuracy t (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le
    I.final_budget.mass_positive (I.massAccuracy_le_level 0 (by omega)) ht hG.1 hG.2 hQ.1 hQ.2
  have hK : (mainTruePencil I S C t)ᵀ=mainTruePencil I S C t := by
    have hGsym := (posDef_of_half_identity_le _ (hg.gram_bands I S C).1).isHermitian
    have hBm := (constructedNeumannMass_posDef _ hGsym I.massAccuracy I.final_budget.mass_positive).isHermitian.eq
    have hQsym := (mainTrueRightGram_posSemidef I S C).isHermitian.eq
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hBm hQsym
    simp only [mainTruePencil, trueNeumannPencil, Matrix.transpose_sub, Matrix.transpose_smul, hBm, hQsym]
  have hh := constructed_hierarchy_invariant _ (mainTruePencil I S C t)
    (t • (1 : Core C.pair.dimension)+C.rightGram) (mainFinePencil I S C t)
    (safeAccuracy I) L hD hK
    (by simpa only [safeAccuracy_eq I 0 (by omega), mainTruePencil] using hbase)
    (fun j hj => safeAccuracy_pos I j)
    (fun j hj => by rw [safeAccuracy_eq I j hj]; exact I.accuracy_bounded j hj)
    (fun j hj => by
      rw [safeAccuracy_eq I (j+1) (by omega), safeAccuracy_eq I j (by omega)]
      exact I.refinement_ratio j hj)
    (fun j _ => mainFinePencil_transpose I S C t j)
    (fun j hj => hg.fine_pencil_error kernels I S C t ht.le j hj) L le_rfl
  simpa only [safeAccuracy_eq I L le_rfl, mainRefinedFactor] using hh

end
end HierarchicalAbsoluteSpectral
