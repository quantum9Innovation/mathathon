import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions

/-! The dimensional family constructs its scale, accuracy and entire finite
schedule using only five scalar instructions followed by the root loop. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

structure FamilyScalarParameters (m N : ℝ) where
  ratio : ℝ
  scale : ℝ
  ideal : ℝ
  theta : ℝ
  ratio_eq : ratio = m/N
  scale_eq : scale = Real.sqrt (m/N)
  ideal_eq : ideal = scale/1024
  theta_eq : theta = (m/N)^2*Real.sqrt (m/N)
  scale_positive : 0 < scale
  ideal_positive : 0 < ideal
  schedule : FamilyScheduleOutput (1/1024) ideal

def familyScalarProgram (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    ArithmeticProgram (FamilyScalarParameters m N) :=
  .certifiedStep (.div m N) (fun ρ =>
  .certifiedStep (.sqrt ρ.val) (fun s =>
  .certifiedStep (.div s.val 1024) (fun hstar =>
  .certifiedStep (.mul ρ.val ρ.val) (fun ρ₂ =>
  .certifiedStep (.mul ρ₂.val s.val) (fun θ =>
    have hρ : ρ.val = m/N := ρ.property
    have hscale : s.val = Real.sqrt (m/N) := by rw [s.property,hρ]; rfl
    have hideal : hstar.val = s.val/1024 := hstar.property
    have hs : 0 < s.val := by rw [hscale]; exact Real.sqrt_pos.mpr (div_pos hm hN)
    have hi : 0 < hstar.val := by rw [hideal]; positivity
    do
      let out ← familyScheduleProgram (1/1024) hstar.val (by norm_num) hi
      ArithmeticProgram.pure
        { ratio := ρ.val
          scale := s.val
          ideal := hstar.val
          theta := θ.val
          ratio_eq := hρ
          scale_eq := hscale
          ideal_eq := hideal
          theta_eq := by
            rw [θ.property,ρ₂.property]
            change (ρ.val*ρ.val)*s.val = _
            rw [hscale,hρ]
            ring
          scale_positive := hs
          ideal_positive := hi
          schedule := out })))))

theorem familyScalarProgram_admissible (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    (familyScalarProgram m N hm hN).admissible := by
  unfold familyScalarProgram
  simp only [ArithmeticProgram.admissible,ArithmeticOp.admissible,ArithmeticOp.eval,
    admissible_bind,admissible_pure,and_true,true_and]
  exact ⟨hN.ne',(div_pos hm hN).le,by norm_num,
    (familyScheduleProgram_checked (1/1024) (Real.sqrt (m/N)/1024) (by norm_num) (by positivity)).1⟩

theorem familyScalarProgram_work (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    (familyScalarProgram m N hm hN).work =
      4*(familyScalarProgram m N hm hN).eval.schedule.depth+9 := by
  have hw := (familyScheduleProgram_checked (1/1024) (Real.sqrt (m/N)/1024)
    (by norm_num) (by positivity : 0 < Real.sqrt (m/N)/1024)).2.1
  simp only [familyScalarProgram,ArithmeticProgram.work,ArithmeticProgram.eval,ArithmeticOp.eval,
    work_bind,work_pure,eval_bind,eval_pure,add_zero]
  rw [hw]
  simp only [eval_bind,eval_pure]
  omega

def FamilyScalarParameters.schedule_scale {m N : ℝ} (out : FamilyScalarParameters m N) :
    FamilyScheduleOutput (1/1024) (Real.sqrt (m/N)/1024) := by
  rw [← out.scale_eq,← out.ideal_eq]
  exact out.schedule

end
end HierarchicalAbsoluteSpectral
