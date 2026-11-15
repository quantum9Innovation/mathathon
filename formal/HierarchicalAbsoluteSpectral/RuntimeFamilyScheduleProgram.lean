import HierarchicalAbsoluteSpectral.RuntimeFamilyScheduleScalar

/-! The finite square-root schedule executes its stopping test. Every
accepted level is certified; a separate base fallback is selected precisely
when no level was accepted. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

structure FamilyScheduleOutput (h hstar : ℝ) where
  depth : ℕ
  terminal : ℝ
  terminal_eq : terminal = familyScheduleValue h hstar depth
  ratios : ∀ j < depth,
    familyScheduleValue h hstar (j+1) ≤ familyScheduleValue h hstar j/1024
  stopped : ¬Real.sqrt (terminal*hstar) ≤ terminal/1024

def familyScheduleProgram (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    ArithmeticProgram (FamilyScheduleOutput h hstar) :=
  .certifiedStep (.mul h hstar) (fun p =>
  .certifiedStep (.sqrt p.val) (fun c =>
  .certifiedStep (.div h 1024) (fun t =>
  have hc : c.val = Real.sqrt (h*hstar) := by rw [c.property,p.property]; rfl
  have ht : t.val = h/1024 := by rw [t.property]; rfl
  have hcp : 0 < c.val := by rw [hc]; exact Real.sqrt_pos.mpr (mul_pos hh hs)
  .branch c.val t.val
    (fun ha => do
      let out ← familyScheduleProgram c.val hstar hcp hs
      ArithmeticProgram.pure
        { depth := out.depth+1
          terminal := out.terminal
          terminal_eq := by rw [familyScheduleValue_shift,← hc]; exact out.terminal_eq
          ratios := by
            intro j hj
            cases j with
            | zero => simpa only [familyScheduleValue,← hc,← ht] using ha
            | succ j =>
                rw [familyScheduleValue_shift h hstar (j+1),familyScheduleValue_shift h hstar j,← hc]
                exact out.ratios j (by omega)
          stopped := out.stopped })
    (fun ha => ArithmeticProgram.pure
      { depth := 0
        terminal := h
        terminal_eq := rfl
        ratios := by omega
        stopped := by simpa only [← hc,← ht] using ha }))))
termination_by familyScheduleMeasure h hstar
decreasing_by
  apply lt_of_le_of_lt (le_refl _)
  rw [hc]
  exact familyScheduleMeasure_decreases h hstar hh hs (by rwa [← hc,← ht])

theorem familyScheduleProgram_checked (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    (familyScheduleProgram h hstar hh hs).admissible ∧
    (familyScheduleProgram h hstar hh hs).work =
      4*((familyScheduleProgram h hstar hh hs).eval.depth+1) ∧
    (familyScheduleProgram h hstar hh hs).eval.depth ≤ familyScheduleMeasure h hstar := by
  have heq := familyScheduleProgram.eq_def h hstar hh hs
  simp only [heq,ArithmeticProgram.admissible,ArithmeticProgram.eval,ArithmeticProgram.work,
    ArithmeticOp.eval,ArithmeticOp.admissible,true_and]
  by_cases ha : Real.sqrt (h*hstar) ≤ h/1024
  · have hc : 0 < Real.sqrt (h*hstar) := Real.sqrt_pos.mpr (mul_pos hh hs)
    have ih := familyScheduleProgram_checked (Real.sqrt (h*hstar)) hstar hc hs
    have hm := familyScheduleMeasure_decreases h hstar hh hs ha
    simp only [ArithmeticProgram.admissible,ArithmeticProgram.eval,ArithmeticProgram.work,
      dif_pos ha,admissible_bind,admissible_pure,eval_bind,eval_pure,work_bind,work_pure,
      add_zero,and_true]
    refine ⟨⟨by positivity,by norm_num,ih.1⟩,?_,?_⟩
    · rw [ih.2.1]
      omega
    · omega
  · simp only [ArithmeticProgram.admissible,ArithmeticProgram.eval,ArithmeticProgram.work,
      dif_neg ha,admissible_pure,eval_pure,work_pure]
    exact ⟨⟨by positivity,by norm_num,trivial⟩,trivial,Nat.zero_le _⟩
termination_by familyScheduleMeasure h hstar
decreasing_by exact familyScheduleMeasure_decreases h hstar hh hs ha

theorem FamilyScheduleOutput.level_le {h hstar : ℝ} (out : FamilyScheduleOutput h hstar)
    (hh : 0 < h) (hs : 0 < hstar) :
    ∀ j ≤ out.depth, familyScheduleValue h hstar j ≤ h := by
  intro j hj
  induction j with
  | zero => exact le_refl _
  | succ j ih =>
    have hp := familyScheduleValue_pos h hstar hh hs j
    have ha := out.ratios j (by omega)
    exact ha.trans (by nlinarith [ih (by omega)])

theorem FamilyScheduleOutput.terminal_positive {h hstar : ℝ} (out : FamilyScheduleOutput h hstar)
    (hh : 0 < h) (hs : 0 < hstar) : 0 < out.terminal := by
  rw [out.terminal_eq]
  exact familyScheduleValue_pos h hstar hh hs _

theorem FamilyScheduleOutput.level_antitone {h hstar : ℝ} (out : FamilyScheduleOutput h hstar)
    (hh : 0 < h) (hs : 0 < hstar) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ out.depth) :
    familyScheduleValue h hstar j ≤ familyScheduleValue h hstar i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
    have hp := familyScheduleValue_pos h hstar hh hs j
    have ha := out.ratios j (by omega)
    exact ha.trans (le_trans (by nlinarith : familyScheduleValue h hstar j/1024 ≤
      familyScheduleValue h hstar j) (ih (by omega)))

theorem FamilyScheduleOutput.nonzero_terminal_bounds {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth) :
    s ≤ out.terminal ∧ out.terminal < 1024*s := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  apply familySchedule_terminal_bounds s out.terminal hs
    (out.terminal_positive (by norm_num) (by positivity)) _ out.stopped
  refine ⟨familyScheduleValue (1/1024) (s/1024) j,
    familyScheduleValue_pos _ _ (by norm_num) (by positivity) j,?_,?_⟩
  · rw [out.terminal_eq,hj]
    rfl
  · rw [out.terminal_eq,hj]
    exact out.ratios j (by omega)

theorem FamilyScheduleOutput.level_bounds {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (j : ℕ) (hj : j ≤ out.depth) :
    s ≤ familyScheduleValue (1/1024) (s/1024) j ∧
      familyScheduleValue (1/1024) (s/1024) j ≤ 1/1024 := by
  have hterminal : s ≤ out.terminal := (out.nonzero_terminal_bounds hs hL).1
  rw [out.terminal_eq] at hterminal
  exact ⟨hterminal.trans (out.level_antitone (by norm_num) (by positivity) hj (le_refl _)),
    out.level_le (by norm_num) (by positivity) j hj⟩

theorem FamilyScheduleOutput.no_level_fallback {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : out.depth = 0) :
    (1/1024 : ℝ)^4 < s^2 := by
  have he : out.terminal = 1/1024 := by rw [out.terminal_eq,hL]; rfl
  have ht := out.stopped
  rw [he] at ht
  have hn := mt (familySchedule_accept_iff (1/1024) (s/1024) (by norm_num) (by positivity)).mpr ht
  have hp : (1/1024 : ℝ)^2 < s := by nlinarith [lt_of_not_ge hn]
  nlinarith

theorem FamilyScheduleOutput.depth_power_bounds {s : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth) :
    Real.log (1/s)/(2*Real.log 1024) < (2 : ℝ)^out.depth ∧
      (2 : ℝ)^out.depth ≤ Real.log (1/s)/Real.log 1024 := by
  have hb := out.nonzero_terminal_bounds hs hL
  have hp := out.terminal_positive (by norm_num) (by positivity)
  have hs0 : 0 < s/1024 := by positivity
  have he : Real.log (out.terminal/(s/1024)) = Real.log (1/s)/(2 : ℝ)^out.depth := by
    rw [out.terminal_eq,familySchedule_log_value _ _ (by norm_num) hs0]
    congr 2
    field_simp
  have hlo : (1024 : ℝ) ≤ out.terminal/(s/1024) :=
    (le_div_iff₀ hs0).mpr (by nlinarith)
  have hup : out.terminal/(s/1024) < (1024 : ℝ)^2 :=
    (div_lt_iff₀ hs0).mpr (by nlinarith)
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) hlo
  have hlogup := Real.log_lt_log (div_pos hp hs0) hup
  rw [Real.log_pow] at hlogup
  rw [he] at hloglo hlogup
  have heps : 0 < Real.log 1024 := Real.log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ)^out.depth := by positivity
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 2*Real.log 1024)).mpr
    have hh := (div_lt_iff₀ hpow).mp hlogup
    nlinarith
  · apply (le_div_iff₀ heps).mpr
    have hh := (le_div_iff₀ hpow).mp hloglo
    nlinarith

theorem FamilyScheduleOutput.no_level_finite_size {s m c : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hc : 0 < c)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : out.depth = 0)
    (hscale : c*Real.log m ≤ Real.log (1/s)) :
    m < Real.exp (2*Real.log 1024/c) := by
  have he : out.terminal = 1/1024 := by rw [out.terminal_eq,hL]; rfl
  have ht := out.stopped
  rw [he] at ht
  have hn := mt (familySchedule_accept_iff (1/1024) (s/1024) (by norm_num) (by positivity)).mpr ht
  have hp : 1/s < (1024 : ℝ)^2 := (div_lt_iff₀ hs).mpr (by nlinarith [lt_of_not_ge hn])
  have hl := Real.log_lt_log (one_div_pos.mpr hs) hp
  rw [Real.log_pow] at hl
  apply (Real.log_lt_iff_lt_exp hm).mp
  exact (lt_div_iff₀ hc).mpr (by nlinarith)

end
end HierarchicalAbsoluteSpectral
