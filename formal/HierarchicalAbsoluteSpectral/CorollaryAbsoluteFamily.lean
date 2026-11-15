import HierarchicalAbsoluteSpectral.CorollaryAbsolute
import HierarchicalAbsoluteSpectral.CorollaryAbsolutePrepared
import HierarchicalAbsoluteSpectral.MainFamilyProgramParameters

/-! The family caller takes only factors, dimensions, confidence and an
absolute tolerance. Its scalar schedule includes the executed finite
no-level branch. A smaller internal theta decreases the slack rank. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {N m : ℕ}

structure AbsoluteFamilyProblem (N m : ℕ) where
  A : Matrix (Fin N) (Fin m) ℝ
  B : Matrix (Fin m) (Fin N) ℝ
  delta : ℝ
  tolerance : ℝ
  core_positive : 1 ≤ m
  core_le_side : m ≤ N
  delta_positive : 0 < delta
  delta_lt_one : delta < 1
  tolerance_positive : 0 < tolerance

def AbsoluteFamilyProblem.seed (I : AbsoluteFamilyProblem N m) : FamilyProblem N m 1 where
  A := I.A
  B := I.B
  delta := I.delta/((m:ℝ)+1)
  core_le_side := I.core_le_side
  rank_positive := le_rfl
  rank_le_sqrt := by
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.le_sqrt.mpr (by simpa using I.core_positive)
  delta_positive := div_pos I.delta_positive (by positivity)
  delta_lt_one := by
    apply (div_lt_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr
    linarith [I.delta_lt_one,Nat.cast_nonneg m]

def AbsoluteFamilyProblem.theta (I : AbsoluteFamilyProblem N m) : ℝ := I.seed.theta

def AbsoluteFamilyProblem.slackRank (I : AbsoluteFamilyProblem N m) : ℕ :=
  absoluteSlackRank I.A I.B I.tolerance I.theta I.tolerance_positive I.seed.theta_positive.le

def FixedProblem.absoluteProblem {n m p r L : ℕ} (J : FixedProblem n m p r L)
    (e : ℝ) (he : 0 < e) : AbsoluteProblem n m p L where
  A := J.A
  B := J.B
  theta := J.theta
  delta := J.delta
  tolerance := e
  accuracy := J.accuracy
  core_positive := J.rank_positive.trans J.rank_le_core
  core_le_rows := J.core_le_rows
  core_le_cols := J.core_le_cols
  depth_positive := J.depth_positive
  theta_positive := J.theta_positive
  delta_positive := J.delta_positive
  delta_lt_one := J.delta_lt_one
  tolerance_positive := he
  accuracy_positive := J.accuracy_positive
  initial_accuracy_le := J.initial_accuracy_le
  theta_le_last := J.theta_le_last
  refinement_ratio := J.refinement_ratio

def AbsoluteFamilyProblem.absoluteFromPrepared (I : AbsoluteFamilyProblem N m)
    (P : PreparedFamilyProblem I.seed) : AbsoluteProblem N m N P.depth :=
  { P.fixed.absoluteProblem I.tolerance I.tolerance_positive with
      delta := I.delta
      delta_positive := I.delta_positive
      delta_lt_one := I.delta_lt_one }

def AbsoluteFamilyProblem.fixed (I : AbsoluteFamilyProblem N m) :
    AbsoluteProblem N m N I.seed.prepared.depth := I.absoluteFromPrepared I.seed.prepared

theorem FixedProblem.eq_of_data {n m p r L : ℕ} (I J : FixedProblem n m p r L)
    (hA : I.A=J.A) (hB : I.B=J.B) (hθ : I.theta=J.theta) (hδ : I.delta=J.delta)
    (hh : I.accuracy=J.accuracy) : I=J := by
  cases I
  cases J
  simp_all

theorem AbsoluteFamilyProblem.fixed_seed_eq (I : AbsoluteFamilyProblem N m) :
    I.fixed.seed=I.seed.prepared.fixed := by
  apply FixedProblem.eq_of_data
  · rfl
  · rfl
  · rfl
  · exact I.seed.prepared.input_failure.symm
  · rfl

theorem AbsoluteFamilyProblem.internal_slackRank_le (I : AbsoluteFamilyProblem N m) :
    I.fixed.slackRank ≤ I.slackRank := by
  change absoluteSlackRank I.seed.prepared.fixed.A I.seed.prepared.fixed.B I.tolerance
    I.seed.prepared.fixed.theta I.tolerance_positive I.seed.prepared.fixed.theta_positive.le ≤ _
  rw [I.seed.prepared.input_left,I.seed.prepared.input_right]
  exact absoluteSlackRank_mono_theta I.A I.B I.tolerance _ I.theta I.tolerance_positive
    I.seed.prepared.fixed.theta_positive.le I.seed.theta_positive.le I.seed.prepared.internal_accuracy_le

abbrev AbsoluteFamilyTape (I : AbsoluteFamilyProblem N m) := AbsoluteTape I.fixed

def absoluteFamilyRandomLaw (I : AbsoluteFamilyProblem N m) : Measure (AbsoluteFamilyTape I) :=
  absoluteRandomLaw I.fixed

instance absoluteFamilyRandomLaw_isProbability (I : AbsoluteFamilyProblem N m) :
    IsProbabilityMeasure (absoluteFamilyRandomLaw I) := by unfold absoluteFamilyRandomLaw; infer_instance

def absoluteFamilyContinuation (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (P : {P : PreparedFamilyProblem I.seed // P=I.seed.prepared}) :
    ArithmeticProgram (AbsoluteOutput N N m) :=
  preparedAbsoluteAlgorithmProgram kernels (I.absoluteFromPrepared P.val)
    (cast (congrArg (fun P : PreparedFamilyProblem I.seed =>
      AbsoluteTape (I.absoluteFromPrepared P)) P.property.symm) g)

theorem absoluteFamilyContinuation_eq (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (P : {P : PreparedFamilyProblem I.seed // P=I.seed.prepared}) :
    absoluteFamilyContinuation kernels I g P=preparedAbsoluteAlgorithmProgram kernels I.fixed g := by
  rcases P with ⟨P,hP⟩
  subst P
  rfl

def absoluteFamilyProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) : ArithmeticProgram (AbsoluteOutput N N m) := do
  let P ← certifyAs (familyPreparationProgram I.seed) I.seed.prepared rfl
  absoluteFamilyContinuation kernels I g P

theorem absoluteFamilyProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    (absoluteFamilyProgram kernels I g).eval=(absoluteAlgorithmProgram kernels I.fixed g).eval := by
  simp only [absoluteFamilyProgram,eval_bind,absoluteFamilyContinuation_eq,preparedAbsoluteAlgorithmProgram_eval]

theorem absoluteFamilyProgram_work (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    (absoluteFamilyProgram kernels I g).work=(familyPreparationProgram I.seed).work+
      (preparedAbsoluteAlgorithmProgram kernels I.fixed g).work := by
  simp only [absoluteFamilyProgram,work_bind,certifyAs_work,absoluteFamilyContinuation_eq]

theorem absoluteFamilyProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I) :
    (absoluteFamilyProgram kernels I g).admissible := by
  simp only [absoluteFamilyProgram,admissible_bind,certifyAs_admissible,familyPreparationProgram_admissible,
    absoluteFamilyContinuation_eq,preparedAbsoluteAlgorithmProgram_admissible,and_self]

theorem absolute_family_error_without_supplied_rank
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : AbsoluteFamilyProblem N m) :
    ∃ E : Set (AbsoluteFamilyTape I), MeasurableSet E ∧
      (absoluteFamilyRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (absoluteFamilyProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_error_without_supplied_rank kernels I.fixed
  refine ⟨E,hEm,?_,?_⟩
  · exact hEp
  · intro g hg
    obtain ⟨hw,he⟩ := hE g hg
    rw [absoluteFamilyProgram_eval]
    refine ⟨hw.trans (Nat.mul_le_mul_left 2 I.internal_slackRank_le),?_⟩
    simpa only [AbsoluteFamilyProblem.fixed,AbsoluteFamilyProblem.absoluteFromPrepared,FixedProblem.absoluteProblem,
      I.seed.prepared.input_left,I.seed.prepared.input_right] using he

end
end HierarchicalAbsoluteSpectral
