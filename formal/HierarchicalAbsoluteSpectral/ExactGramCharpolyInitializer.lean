import HierarchicalAbsoluteSpectral.ExactGramCharpolyCoeff
import HierarchicalAbsoluteSpectral.ProbabilityInitializerProgram

/-!
The original exact characteristic-coefficient initializer. Its input is a
materialized polynomial coefficient table. Coefficient computation is a
separate caller obligation; this file charges every scalar operation used
to turn that table into the bracket.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open ArithmeticProgram hiding pure

def exactGramCoeffInitializerProgram {k : ℕ} (p : Polynomial ℝ) (j : Fin k)
    (stretch : ℝ) : ArithmeticProgram InitializerResult := do
  let numerator ← mul ((-1 : ℝ)^(j.val+1)) (p.coeff (k-(j.val+1)))
  let denominator ← mul ((-1 : ℝ)^j.val) (p.coeff (k-j.val))
  .branch numerator 0
    (fun _ => .pure .exact)
    (fun _ => do
      let ratio ← div numerator denominator
      let scale ← mul stretch (k : ℝ)
      let lower ← div ratio scale
      let upper ← mul scale ratio
      ArithmeticProgram.pure (.bracket lower upper))

@[simp] theorem exactGramCoeffInitializerProgram_eval {k : ℕ} (p : Polynomial ℝ)
    (j : Fin k) (stretch : ℝ) :
    (exactGramCoeffInitializerProgram p j stretch).eval =
      if exactGramSignedCoeff p k (j.val+1) ≤ 0 then .exact
      else .bracket
        ((exactGramSignedCoeff p k (j.val+1) / exactGramSignedCoeff p k j.val) /
          (stretch*k))
        ((stretch*k) *
          (exactGramSignedCoeff p k (j.val+1) / exactGramSignedCoeff p k j.val)) := by
  by_cases h : exactGramSignedCoeff p k (j.val+1) ≤ 0 <;>
    simp [exactGramCoeffInitializerProgram, exactGramSignedCoeff, ArithmeticProgram.eval] at h ⊢

theorem exactGramCoeffInitializerProgram_work_le {k : ℕ} (p : Polynomial ℝ)
    (j : Fin k) (stretch : ℝ) :
    (exactGramCoeffInitializerProgram p j stretch).work ≤ 7 := by
  simp only [exactGramCoeffInitializerProgram, work_bind, work_mul, eval_mul,
    ArithmeticProgram.work]
  split <;> simp

theorem exactGramCoeffInitializerProgram_admissible {k : ℕ} (A : Core k)
    (hA : A.PosSemidef) (j : Fin k) (stretch : ℝ) (hstretch : 0 < stretch) :
    (exactGramCoeffInitializerProgram A.charpoly j stretch).admissible := by
  have hk : (0:ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  by_cases h : exactGramSignedCoeff A.charpoly k (j.val+1) ≤ 0
  · simp only [exactGramSignedCoeff] at h
    simp only [exactGramCoeffInitializerProgram, admissible_bind, admissible_mul,
      eval_mul, true_and, ArithmeticProgram.admissible, dif_pos h]
  · have hnum : 0 < exactGramSignedCoeff A.charpoly k (j.val+1) :=
      lt_of_not_ge h
    have hv := (exactGramSignedCoeff_pos_iff A hA j).mp hnum
    have hden := (exactGram_charpoly_ratio A hA j hv).1
    simp only [exactGramSignedCoeff] at h hden
    simp only [exactGramCoeffInitializerProgram, admissible_bind, admissible_mul,
      eval_mul, true_and, ArithmeticProgram.admissible, dif_neg h,
      admissible_div]
    exact ⟨hden.ne', (mul_pos hstretch hk).ne', trivial⟩

theorem exactGramCoeffInitializer_ratio_bounds {k : ℕ} (A : Core k)
    (hA : A.PosSemidef) (j : Fin k)
    (hj : 0 < orderedEigenvalue A hA.isHermitian j) :
    let ratio := exactGramSignedCoeff A.charpoly k (j.val+1) /
      exactGramSignedCoeff A.charpoly k j.val
    0 < ratio ∧ ratio / k ≤ orderedEigenvalue A hA.isHermitian j ∧
      orderedEigenvalue A hA.isHermitian j ≤ k * ratio := by
  dsimp only
  obtain ⟨hden,hlo,hup⟩ := exactGram_charpoly_ratio A hA j hj
  have hk : (0:ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  have hindex : (0:ℝ) < ((j.val+1 : ℕ) : ℝ) := by positivity
  have hr : 0 < exactGramSignedCoeff A.charpoly k (j.val+1) /
      exactGramSignedCoeff A.charpoly k j.val :=
    div_pos ((exactGramSignedCoeff_pos_iff A hA j).mpr hj) hden
  refine ⟨hr, ?_, ?_⟩
  · rw [div_le_iff₀ hk]
    have hc : ((k-j.val : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k j.val
    exact hup.trans (by nlinarith)
  · have hidx : ((j.val+1 : ℕ) : ℝ) ≤ k := by exact_mod_cast j.isLt
    have hh := (div_le_iff₀ hindex).mp hlo
    nlinarith

/-- With `stretch=1` this is the plain positive bracket in the appendix;
with `stretch=4` it gives the manuscript's `16 k²` bracket for a target
within a factor four of the coarse eigenvalue. -/
theorem exactGramCoeffInitializerProgram_correct {k : ℕ} (A : Core k)
    (hA : A.PosSemidef) (j : Fin k) (stretch target : ℝ) (hstretch : 1 ≤ stretch)
    (hcompare : orderedEigenvalue A hA.isHermitian j / stretch ≤ target ∧
      target ≤ stretch * orderedEigenvalue A hA.isHermitian j) :
    match (exactGramCoeffInitializerProgram A.charpoly j stretch).eval with
    | .exact => target = 0
    | .bracket lower upper =>
        0 < lower ∧ lower ≤ target ∧ target ≤ upper ∧
          upper / lower = (stretch * k)^2 := by
  have hs : 0 < stretch := lt_of_lt_of_le (by norm_num) hstretch
  have hk : (0:ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  rw [exactGramCoeffInitializerProgram_eval]
  split_ifs with h
  · have hv : orderedEigenvalue A hA.isHermitian j = 0 := by
      apply le_antisymm _ (orderedEigenvalue_nonneg A hA j)
      by_contra hv
      have hh := (exactGramSignedCoeff_pos_iff A hA j).mpr (lt_of_not_ge hv)
      linarith
    apply le_antisymm
    · simpa only [hv, mul_zero] using hcompare.2
    · simpa only [hv, zero_div] using hcompare.1
  · have hv := (exactGramSignedCoeff_pos_iff A hA j).mp (lt_of_not_ge h)
    obtain ⟨hr,hlo,hup⟩ := exactGramCoeffInitializer_ratio_bounds A hA j hv
    have hsk : 0 < stretch * (k:ℝ) := mul_pos hs hk
    refine ⟨div_pos hr hsk, ?_, ?_, ?_⟩
    · apply le_trans _ hcompare.1
      rw [mul_comm stretch (k:ℝ), div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right hlo hs.le
    · apply le_trans hcompare.2
      have hh := mul_le_mul_of_nonneg_left hup hs.le
      simpa only [mul_assoc] using hh
    · set ratio := exactGramSignedCoeff A.charpoly k (j.val+1) /
        exactGramSignedCoeff A.charpoly k j.val
      field_simp [hr.ne', hs.ne', hk.ne']
      <;> ring

end
end HierarchicalAbsoluteSpectral
