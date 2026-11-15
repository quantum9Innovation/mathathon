import HierarchicalAbsoluteSpectral.RuntimeFamilyParameterProgram
import HierarchicalAbsoluteSpectral.RuntimeFamilySequences
import HierarchicalAbsoluteSpectral.MainProblem

/-! Original integer-dimensional inputs for the growing-depth algorithm.
The preparation program executes the square-root schedule, stores all of its
accuracies, and constructs the fixed-depth input used by the main program.
The zero-depth case uses a fixed one-refinement schedule at a smaller internal
accuracy, so it preserves the same rank cap even for the finite exceptions. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

structure FamilyProblem (N m r : ℕ) where
  A : Matrix (Fin N) (Fin m) ℝ
  B : Matrix (Fin m) (Fin N) ℝ
  delta : ℝ
  core_le_side : m ≤ N
  rank_positive : 1 ≤ r
  rank_le_sqrt : r ≤ ⌊Real.sqrt (m : ℝ)⌋₊
  delta_positive : 0 < delta
  delta_lt_one : delta < 1

namespace FamilyProblem

def theta (I : FamilyProblem N m r) : ℝ := (m/N : ℝ)^2*Real.sqrt (m/N : ℝ)

theorem rank_le_core (I : FamilyProblem N m r) : r ≤ m := by
  exact I.rank_le_sqrt.trans (by rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]; exact Nat.sqrt_le_self m)

theorem core_positive (I : FamilyProblem N m r) : 0 < m := by
  have := I.rank_le_core
  have := I.rank_positive
  omega

theorem side_positive (I : FamilyProblem N m r) : 0 < N := I.core_positive.trans_le I.core_le_side

theorem ratio_positive (I : FamilyProblem N m r) : 0 < (m/N : ℝ) := by
  exact div_pos (by exact_mod_cast I.core_positive) (by exact_mod_cast I.side_positive)

theorem ratio_le_one (I : FamilyProblem N m r) : (m/N : ℝ) ≤ 1 := by
  apply (div_le_one (by exact_mod_cast I.side_positive)).mpr
  exact_mod_cast I.core_le_side

theorem theta_positive (I : FamilyProblem N m r) : 0 < I.theta := by
  unfold theta
  exact mul_pos (pow_pos I.ratio_positive _) (Real.sqrt_pos.mpr I.ratio_positive)

theorem theta_le_scale (I : FamilyProblem N m r) : I.theta ≤ Real.sqrt (m/N : ℝ) := by
  have hρ := I.ratio_positive
  have hρ1 := I.ratio_le_one
  have hs := Real.sqrt_nonneg (m/N : ℝ)
  unfold theta
  have hsq : (m/N : ℝ)^2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hs]

theorem rounded_rank_width (I : FamilyProblem N m r) :
    (r+1 : ℝ) ≤ 2*Real.sqrt (m : ℝ) ∧ r+1 ≤ 2*⌈Real.sqrt (m : ℝ)⌉₊ :=
  family_rounded_rank_width m r I.core_positive I.rank_le_sqrt

end FamilyProblem

/-- An executed table; no square root is hidden in a later accuracy lookup. -/
def familyAccuracyArrayProgram (h hstar : ℝ) :
    (L : ℕ) → ArithmeticProgram (Fin (L+1) → ℝ)
  | 0 => .pure (fun _ => h)
  | L+1 => do
      let product ← mul h hstar
      let next ← sqrt product
      let tail ← familyAccuracyArrayProgram next hstar L
      .pure (Fin.cons h tail)

theorem familyAccuracyArrayProgram_eval (h hstar : ℝ) (L : ℕ) :
    (familyAccuracyArrayProgram h hstar L).eval =
      fun j => familyScheduleValue h hstar j.val := by
  induction L generalizing h with
  | zero =>
    funext j
    have hj : j.val = 0 := by omega
    simp [familyAccuracyArrayProgram,familyScheduleValue,hj]
  | succ L ih =>
    simp only [familyAccuracyArrayProgram,eval_bind,eval_mul,eval_sqrt,eval_pure,ih]
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [familyScheduleValue]
    · simp only [Fin.cons_succ,Fin.val_succ,familyScheduleValue_shift]

theorem familyAccuracyArrayProgram_work (h hstar : ℝ) (L : ℕ) :
    (familyAccuracyArrayProgram h hstar L).work = 2*L := by
  induction L generalizing h with
  | zero => rfl
  | succ L ih => simp [familyAccuracyArrayProgram,ih]; omega

theorem familyAccuracyArrayProgram_admissible (h hstar : ℝ) (hh : 0 ≤ h)
    (hs : 0 ≤ hstar) (L : ℕ) : (familyAccuracyArrayProgram h hstar L).admissible := by
  induction L generalizing h with
  | zero => trivial
  | succ L ih =>
    simp only [familyAccuracyArrayProgram,admissible_bind,admissible_mul,eval_mul,
      admissible_sqrt,eval_sqrt,admissible_pure,and_true,true_and]
    exact ⟨mul_nonneg hh hs,ih _ (Real.sqrt_nonneg _)⟩

def storedFamilyAccuracy {L : ℕ} (values : Fin (L+1) → ℝ) (j : ℕ) : ℝ :=
  values ⟨min j L,by omega⟩

theorem storedFamilyAccuracy_eq {L : ℕ} (values : Fin (L+1) → ℝ) (j : ℕ)
    (hj : j ≤ L) : storedFamilyAccuracy values j = values ⟨j,by omega⟩ := by
  simp [storedFamilyAccuracy,Nat.min_eq_left hj]

theorem familyScalarSchedule_terminal_bounds (out : FamilyScalarParameters (m : ℝ) (N : ℝ))
    (hL : 0 < out.schedule.depth) :
    out.scale ≤ out.schedule.terminal ∧ out.schedule.terminal < 1024*out.scale := by
  rcases out with ⟨ρ,scale,ideal,theta,hρ,hscale,hideal,hθ,hs,hi,schedule⟩
  dsimp only at *
  subst ideal
  exact schedule.nonzero_terminal_bounds hs hL

structure PreparedFamilyProblem (I : FamilyProblem N m r) where
  scalars : FamilyScalarParameters (m : ℝ) (N : ℝ)
  depth : ℕ
  fixed : FixedProblem N m N r depth
  input_left : fixed.A = I.A
  input_right : fixed.B = I.B
  input_failure : fixed.delta = I.delta
  internal_accuracy_le : fixed.theta ≤ I.theta
  depth_eq : depth = if scalars.schedule.depth = 0 then 1 else scalars.schedule.depth
  normal_theta : scalars.schedule.depth ≠ 0 → fixed.theta = I.theta
  normal_accuracy : scalars.schedule.depth ≠ 0 →
    ∀ j ≤ depth, fixed.accuracy j = familyScheduleValue (1/1024) scalars.ideal j

def preparedFamilyNormal (I : FamilyProblem N m r)
    (out : FamilyScalarParameters (m : ℝ) (N : ℝ)) (hL : 0 < out.schedule.depth)
    (values : Fin (out.schedule.depth+1) → ℝ)
    (he : values = fun j => familyScheduleValue (1/1024) out.ideal j.val) :
    PreparedFamilyProblem I where
  scalars := out
  depth := out.schedule.depth
  fixed :=
    { A := I.A, B := I.B, theta := out.theta, delta := I.delta
      accuracy := storedFamilyAccuracy values
      core_le_rows := I.core_le_side, core_le_cols := I.core_le_side
      rank_positive := I.rank_positive, rank_le_core := I.rank_le_core
      depth_positive := by omega
      theta_positive := by rw [out.theta_eq]; exact I.theta_positive
      delta_positive := I.delta_positive, delta_lt_one := I.delta_lt_one
      accuracy_positive := by
        intro j hj
        rw [storedFamilyAccuracy_eq values j hj,he]
        exact familyScheduleValue_pos _ _ (by norm_num) out.ideal_positive j
      initial_accuracy_le := by
        rw [storedFamilyAccuracy_eq values 0 (Nat.zero_le _),he]
        norm_num [familyScheduleValue]
      theta_le_last := by
        rw [storedFamilyAccuracy_eq values _ le_rfl,he]
        change out.theta ≤ familyScheduleValue (1/1024) out.ideal out.schedule.depth
        rw [← out.schedule.terminal_eq,out.theta_eq]
        exact I.theta_le_scale.trans
          (by simpa only [out.scale_eq] using (familyScalarSchedule_terminal_bounds out hL).1)
      refinement_ratio := by
        intro j hj
        rw [storedFamilyAccuracy_eq values (j+1) (by omega),storedFamilyAccuracy_eq values j (by omega),he]
        apply (div_le_iff₀ (familyScheduleValue_pos _ _ (by norm_num) out.ideal_positive j)).mpr
        have hr := out.schedule.ratios j hj
        dsimp only
        nlinarith }
  input_left := rfl
  input_right := rfl
  input_failure := rfl
  internal_accuracy_le := by change out.theta ≤ I.theta; exact out.theta_eq.le
  depth_eq := by simp [hL.ne']
  normal_theta := by intro _; exact out.theta_eq
  normal_accuracy := by
    intro _ j hj
    change storedFamilyAccuracy values j = _
    rw [storedFamilyAccuracy_eq values j hj,he]

def familyFallbackAccuracy (j : ℕ) : ℝ := if j = 0 then 1/1024 else 1/1048576

def preparedFamilyFallback (I : FamilyProblem N m r)
    (out : FamilyScalarParameters (m : ℝ) (N : ℝ)) (hL : out.schedule.depth = 0)
    (theta : ℝ) (hθ : 0 < theta) (hθI : theta ≤ I.theta) (hθlast : theta ≤ 1/1048576) :
    PreparedFamilyProblem I where
  scalars := out
  depth := 1
  fixed :=
    { A := I.A, B := I.B, theta := theta, delta := I.delta
      accuracy := familyFallbackAccuracy
      core_le_rows := I.core_le_side, core_le_cols := I.core_le_side
      rank_positive := I.rank_positive, rank_le_core := I.rank_le_core
      depth_positive := le_rfl, theta_positive := hθ
      delta_positive := I.delta_positive, delta_lt_one := I.delta_lt_one
      accuracy_positive := by intro j hj; unfold familyFallbackAccuracy; split_ifs <;> norm_num
      initial_accuracy_le := by norm_num [familyFallbackAccuracy]
      theta_le_last := by simpa [familyFallbackAccuracy] using hθlast
      refinement_ratio := by
        intro j hj
        have : j = 0 := by omega
        subst j
        norm_num [familyFallbackAccuracy] }
  input_left := rfl
  input_right := rfl
  input_failure := rfl
  internal_accuracy_le := hθI
  depth_eq := by simp [hL]
  normal_theta := by simp [hL]
  normal_accuracy := by simp [hL]

def familyPreparationProgram (I : FamilyProblem N m r) :
    ArithmeticProgram (PreparedFamilyProblem I) := do
  let out ← familyScalarProgram (m : ℝ) (N : ℝ)
    (by exact_mod_cast I.core_positive) (by exact_mod_cast I.side_positive)
  .branch (out.schedule.depth : ℝ) 0
    (fun hzero =>
      have hz : out.schedule.depth = 0 := by exact_mod_cast Nat.eq_zero_of_le_zero (by exact_mod_cast hzero)
      .branch out.theta (1/1048576)
        (fun hθ => .pure (preparedFamilyFallback I out hz out.theta
          (by rw [out.theta_eq]; exact I.theta_positive) (by rw [out.theta_eq]; exact le_rfl) hθ))
        (fun hθ => .pure (preparedFamilyFallback I out hz (1/1048576) (by norm_num)
          (by
            change 1/1048576 ≤ (m/N : ℝ)^2*Real.sqrt (m/N : ℝ)
            simpa only [out.theta_eq] using (lt_of_not_ge hθ).le) le_rfl)))
    (fun hpositive =>
      have hp : 0 < out.schedule.depth := by
        have : (0 : ℝ) < out.schedule.depth := lt_of_not_ge hpositive
        exact_mod_cast this
      do
        let values ← (familyAccuracyArrayProgram (1/1024) out.ideal out.schedule.depth).certify
        .pure (preparedFamilyNormal I out hp values.val
          (values.property.trans (familyAccuracyArrayProgram_eval _ _ _))))

theorem familyPreparationProgram_admissible (I : FamilyProblem N m r) :
    (familyPreparationProgram I).admissible := by
  unfold familyPreparationProgram
  refine (admissible_bind _ _).mpr ⟨familyScalarProgram_admissible _ _ _ _,?_⟩
  simp only [ArithmeticProgram.admissible]
  split_ifs <;> simp only [admissible_bind,certify_admissible,admissible_pure,and_true]
  exact familyAccuracyArrayProgram_admissible _ _ (by norm_num)
    (le_of_lt (FamilyScalarParameters.ideal_positive _)) _

def FamilyProblem.prepared (I : FamilyProblem N m r) : PreparedFamilyProblem I :=
  (familyPreparationProgram I).eval

def FamilyProblem.scalarParameters (I : FamilyProblem N m r) :
    FamilyScalarParameters (m : ℝ) (N : ℝ) :=
  (familyScalarProgram (m : ℝ) (N : ℝ)
    (by exact_mod_cast I.core_positive) (by exact_mod_cast I.side_positive)).eval

theorem familyPreparationProgram_scalars (I : FamilyProblem N m r) :
    I.prepared.scalars = I.scalarParameters := by
  simp only [FamilyProblem.prepared,familyPreparationProgram,eval_bind,ArithmeticProgram.eval]
  split_ifs <;> simp only [eval_bind,eval_pure,preparedFamilyFallback,preparedFamilyNormal] <;> rfl

theorem familyPreparationProgram_depth (I : FamilyProblem N m r) :
    I.prepared.depth = if I.scalarParameters.schedule.depth = 0 then 1
      else I.scalarParameters.schedule.depth := by
  rw [I.prepared.depth_eq,familyPreparationProgram_scalars]

theorem familyPreparationProgram_work (I : FamilyProblem N m r) :
    (familyPreparationProgram I).work =
      if I.scalarParameters.schedule.depth = 0 then 11 else 6*I.scalarParameters.schedule.depth+10 := by
  unfold familyPreparationProgram
  rw [work_bind,familyScalarProgram_work]
  change 4*I.scalarParameters.schedule.depth+9+_ = _
  by_cases hz : I.scalarParameters.schedule.depth = 0
  · have hr : (I.scalarParameters.schedule.depth : ℝ) ≤ 0 := by rw [hz]; norm_num
    simp only [FamilyProblem.scalarParameters] at hz hr ⊢
    simp [ArithmeticProgram.work,hz]
  · have hr : ¬(I.scalarParameters.schedule.depth : ℝ) ≤ 0 := by
      have hp : 0 < I.scalarParameters.schedule.depth := Nat.pos_of_ne_zero hz
      exact not_le.mpr (by exact_mod_cast hp)
    simp only [FamilyProblem.scalarParameters] at hz hr ⊢
    simp only [ArithmeticProgram.work,dif_neg hr,if_neg hz,work_bind,certify_work,
      familyAccuracyArrayProgram_work,work_pure,add_zero]
    omega

theorem familyPreparationProgram_work_le (I : FamilyProblem N m r) :
    (familyPreparationProgram I).work ≤ 6*I.prepared.depth+11 := by
  rw [familyPreparationProgram_work,familyPreparationProgram_depth]
  split_ifs <;> omega

theorem PreparedFamilyProblem.normal_terminal (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0) :
    Real.sqrt (m/N : ℝ) ≤ P.fixed.accuracy P.depth ∧
      P.fixed.accuracy P.depth < 1024*Real.sqrt (m/N : ℝ) := by
  have hb := familyScalarSchedule_terminal_bounds P.scalars (Nat.pos_of_ne_zero hL)
  have hd : P.depth = P.scalars.schedule.depth := by simpa only [if_neg hL] using P.depth_eq
  rw [P.normal_accuracy hL _ le_rfl,hd,← P.scalars.schedule.terminal_eq]
  simpa only [P.scalars.scale_eq] using hb

end
end HierarchicalAbsoluteSpectral
