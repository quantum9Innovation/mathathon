import HierarchicalAbsoluteSpectral.CorollaryAbsoluteActions

/-! The independent attempted-width bounds on the exact fixed-depth input
used by the absolute family program. Data equality transports the realized
tape and computed sketches, rather than changing the sampled experiment. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Matmul.RectangularPrograms
open scoped BigOperators
variable {N m r s : ℕ}

/-- Equality of fixed input records suffices to use the original realized
tape and support, even though the records contain dependent tape sizes. -/
theorem PreparedFamilyProblem.absolute_six_action_bounds_of_fixed
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I)
    (J : FixedProblem N m N r P.depth) (hJ : J=P.fixed)
    (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape J)
    (C : MainSupportData (mainSketchProgram J g).eval)
    (R : ℕ) (hR : R ≤ ⌊Real.sqrt (m : ℝ)⌋₊) (b : ℕ) (hb : b ≤ R+1) :
    let S := (mainSketchProgram J g).eval
    let M := familyActionWorkScale I P D c χ
    (mainFactorActionCost kernels J S C b P.depth : ℝ) ≤ M ∧
      (mainTrueActionCost kernels J S C b : ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M ∧
      (C.pair.dimension : ℝ)*b ≤ M ∧
      ((kernels N m b).cost : ℝ) ≤ M ∧ ((kernels m C.pair.dimension b).cost : ℝ) ≤ M := by
  subst J
  exact P.absolute_six_action_bounds_of_rank I hL kernels χ hχ hrow D c hD hc hm hmLog
    hscale hδ g C R hR b hb

/-- All six action bounds at the actual family program's fixed input,
for every b up to an independent attempted bound R+1, including R=0. -/
theorem AbsoluteFamilyProblem.fixed_six_action_bounds
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.seed.delta) (g : MainRandomTape I.fixed.seed)
    (C : MainSupportData (mainSketchProgram I.fixed.seed g).eval)
    (R : ℕ) (hR : R ≤ ⌊Real.sqrt (m : ℝ)⌋₊) (b : ℕ) (hb : b ≤ R+1) :
    let S := (mainSketchProgram I.fixed.seed g).eval
    let M := familyActionWorkScale I.seed I.seed.prepared D c χ
    (mainFactorActionCost kernels I.fixed.seed S C b I.seed.prepared.depth : ℝ) ≤ M ∧
      (mainTrueActionCost kernels I.fixed.seed S C b : ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M ∧
      (C.pair.dimension : ℝ)*b ≤ M ∧
      ((kernels N m b).cost : ℝ) ≤ M ∧ ((kernels m C.pair.dimension b).cost : ℝ) ≤ M :=
  I.seed.prepared.absolute_six_action_bounds_of_fixed I.seed I.fixed.seed I.fixed_seed_eq hL
    kernels χ hχ hrow D c hD hc hm hmLog hscale hδ g C R hR b hb

/-- Query-degree bounds on the actual fixed input, uniformly in the
attempted target s. In particular s=0 needs no positive target rank. -/
theorem AbsoluteFamilyProblem.fixed_query_degree_le_combined
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N I.seed.prepared.depth) (C : MainSupportData S)
    (hs : s < C.pair.dimension)
    (D c : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    2*absoluteQueryDegree I.fixed.seed S C hs ≤ familyCombinedDegreeCeiling I.seed D c := by
  rw [I.fixed_seed_eq]
  exact (Nat.mul_le_mul_left 2 (I.seed.prepared.absoluteQuery_degree_le_ceiling I.seed hL S C hs
    D hD hm hscale)).trans (le_max_left _ _)

theorem AbsoluteFamilyProblem.fixed_strong_degree_le_combined
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N I.seed.prepared.depth) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.seed.delta) :
    absoluteStrongDegree I.fixed.seed S C hk ≤ familyCombinedDegreeCeiling I.seed D c := by
  rw [I.fixed_seed_eq]
  exact (I.seed.prepared.absolute_combined_degree_bounds I.seed hL S C D c hD hc hm hscale hδ).2 hk

/-- The two degree ceilings in the interface used by an attempt envelope. -/
theorem AbsoluteFamilyProblem.fixed_degree_bounds
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N I.seed.prepared.depth) (C : MainSupportData S)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.seed.delta) :
    (∀ (s : ℕ) (hs : s < C.pair.dimension),
      absoluteQueryDegree I.fixed.seed S C hs ≤ familyCombinedDegreeCeiling I.seed D c) ∧
      (∀ hk : 1 ≤ C.pair.dimension,
        absoluteStrongDegree I.fixed.seed S C hk ≤ familyCombinedDegreeCeiling I.seed D c) := by
  constructor
  · intro s hs
    have hh := I.fixed_query_degree_le_combined hL S C hs D c hD hm hscale
    omega
  · intro hk
    exact I.fixed_strong_degree_le_combined hL S C hk D c hD hc hm hscale hδ

end
end HierarchicalAbsoluteSpectral
