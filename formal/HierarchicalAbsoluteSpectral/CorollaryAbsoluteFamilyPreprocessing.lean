import HierarchicalAbsoluteSpectral.CorollaryAbsoluteExplicitWork
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalPreprocessing
import HierarchicalAbsoluteSpectral.MainFamilyProgramPreparationCost

/-! The shared preprocessing is paid once. The rank controller pays only
for attempts that it visits; its separate loop factor is logarithmic. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
variable {N m r : ℕ}

theorem absolute_doubling_fuel_log_bound (m : ℕ) (hm : 1 ≤ m)
    (hlog : 1 ≤ Real.log (m:ℝ)) :
    ((Nat.log 2 m+2:ℕ):ℝ) ≤ 4*Real.log (m:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 m) ≤ m := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(Nat.log 2 m)) hp
  rw [Real.log_pow] at hh
  have hl := mul_le_mul_of_nonneg_left family_log_two_lower
    (Nat.cast_nonneg (Nat.log 2 m) : (0:ℝ) ≤ Nat.log 2 m)
  push_cast
  nlinarith only [hh,hl,hlog]

theorem PreparedFamilyProblem.absolute_initial_rows_scale_of_fixed
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (J : FixedProblem N m N r P.depth) (hJ : J=P.fixed)
    (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m:ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N:ℝ)) ≤ D*Real.log (m:ℝ))
    (hδ : (m:ℝ)^(-c) ≤ I.delta) (g : MainRandomTape J) :
    let S := (mainSketchProgram J g).eval
    ((S.levelA 0).1:ℝ) ≤ familyCoarseRowCoefficient D c*(m:ℝ)*(Real.log (m:ℝ))^3 ∧
      ((S.levelB 0).1:ℝ) ≤ familyCoarseRowCoefficient D c*(m:ℝ)*(Real.log (m:ℝ))^3 := by
  subst J
  exact P.actual_initial_rows_scale I hL D c hD hc hm hmLog hscale hδ g

theorem absolute_family_explicit_work_cap_on_sketch_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c M : ℕ, 1 ≤ M → a ≤ M → b ≤ M → c ≤ M →
      ((kernels a b c).cost:ℝ) ≤ Ck*(M:ℝ)^p0)
    (hsketch : MainSketchGood I.fixed.seed (mainSketchProgram I.fixed.seed g.1).eval)
    (hsmall : I.slackRank ≤ Nat.sqrt m/2) :
    let S := (mainSketchProgram I.fixed.seed g.1).eval
    let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
    absoluteFamilyExplicitWork kernels I g ≤ familyFinalRestCap I.seed+6+
      (I.seed.prepared.depth+1)*2*sketchFormationCap N m I.seed.prepared.fixed.sketchFailure+
      coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
      (Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I.fixed S C (2*I.fixed.slackRank) Ck p0 := by
  let S := (mainSketchProgram I.fixed.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  have he := absoluteFamilyExplicitWork_le kernels I g
  rw [absoluteFamilyTotalWork_eq] at he
  have hf := preparedAbsoluteRandomizedWork_small_bound kernels Ck p0 hC hp hK I.fixed g hsketch
    (I.internal_slackRank_le.trans hsmall)
  have hT : I.fixed.seed.queryCap=I.seed.prepared.fixed.queryCap :=
    congrArg (fun J => J.queryCap) I.fixed_seed_eq
  have hR : I.fixed.seed.repetitions=I.seed.prepared.fixed.repetitions :=
    congrArg (fun J => J.repetitions) I.fixed_seed_eq
  have hβ : I.fixed.seed.sketchFailure=I.seed.prepared.fixed.sketchFailure :=
    congrArg (fun J => J.sketchFailure) I.fixed_seed_eq
  dsimp only [absoluteSmallRealizedWorkCap,absolutePreprocessingWorkCap,
    absoluteSharedSketchGaussianDrawCount] at hf
  rw [hT,hR,hβ] at hf
  dsimp only [familyFinalRestCap]
  have hdraws : 0 ≤ I.seed.prepared.fixed.queryCap*I.seed.prepared.fixed.repetitions*
      ((1+1)*m+2*m*m) := Nat.zero_le _
  nlinarith only [he,hf,hdraws]

end
end HierarchicalAbsoluteSpectral
