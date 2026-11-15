import HierarchicalAbsoluteSpectral.MainFamilyProgramActionUniform
import HierarchicalAbsoluteSpectral.MainFamilyProgramCombinedDegree
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamily
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteCost

/-! Uniform action costs for an attempted width independent of the seed
rank. The explicit width inequalities cover zero attempted rank and keep
the same stored sketches, scalar schedule, confidence and arithmetic actions. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Matmul.RectangularPrograms
open scoped BigOperators
variable {N m r s : ℕ}

/-- Any attempted bound through the square-root width is admissible for the
same row kernels, including R=0 and the one-column rank-zero query. -/
theorem absolute_family_action_widths (hm : 2 ≤ m) (R b : ℕ)
    (hR : R ≤ ⌊Real.sqrt (m : ℝ)⌋₊) (hb : b ≤ R+1) :
    b ≤ 2*width (1/2) m ∧ b ≤ m := by
  have hw : R+1 ≤ 2*width (1/2) m := by
    simpa only [width,Real.sqrt_eq_rpow] using
      (family_rounded_rank_width m R (by omega) hR).2
  have hr := hR
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hr
  have hs := Nat.sqrt_lt_self (show 1 < m by omega)
  exact ⟨hb.trans hw,by omega⟩

theorem PreparedFamilyProblem.absolute_weighted_fine_action_bound
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (C : MainSupportData (mainSketchProgram P.fixed g).eval)
    (b : ℕ) (hbWidth : b ≤ 2*width (1/2) m) (j : ℕ) (hj : j < P.depth) :
    P.fixed.accuracy j*((mainFineActionCost kernels P.fixed (mainSketchProgram P.fixed g).eval C j b : ℝ)+
      (C.pair.dimension : ℝ)*b+1) ≤
      familyFineLeafCoefficient D c*χ*((m : ℝ)^2/Real.sqrt (m/N : ℝ))*(Real.log (m : ℝ))^4 := by
  let S := (mainSketchProgram P.fixed g).eval
  let qindex := safeSketchIndex P.depth (j+1)
  let ε := safeAccuracy P.fixed (j+1)/100
  have hε : 0 < ε := div_pos (safeAccuracy_pos P.fixed (j+1)) (by norm_num)
  have hH := P.fixed.accuracy_positive j (by omega)
  have hχ0 : 0 ≤ χ := by linarith
  have hcost := storedFinePencilAction_cost_fixed_row_leaf_bound kernels χ hχ hrow
    (S.levelA qindex).2 (S.levelB qindex).2 C.pair.factor C.pair.leftInverseᵀ 0 ε hε
    I.core_positive (mainSupport_dimension_le S C) hbWidth
  change (mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1 ≤
    4096*(neumannCount ε hε : ℝ)*χ*((S.levelA qindex).1+(S.levelB qindex).1+m : ℕ)*(m : ℝ) at hcost
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hq : (neumannCount ε hε : ℝ) ≤ (4*D+30)*Real.log (m : ℝ) := by
    simpa only [ε,safeAccuracy,Nat.min_eq_left (show j+1 ≤ P.depth by omega)] using
      P.fine_neumann_count_bound I hL D (hlog2.trans hmLog) hscale (j+1) (by omega)
        (div_pos (P.fixed.accuracy_positive (j+1) (by omega)) (by norm_num))
  have hrows := P.weighted_actual_fine_rows I hL D c (by linarith) hc hm hmLog hscale hδ g j hj
  have hleft := mul_le_mul_of_nonneg_left hcost hH.le
  have hqχ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq
    (by norm_num : (0 : ℝ) ≤ 4096)) hχ0
  have hprod := mul_le_mul hqχ hrows (by positivity)
    (by positivity : 0 ≤ 4096*((4*D+30)*Real.log (m : ℝ))*χ)
  calc
    _ ≤ (4096*(neumannCount ε hε : ℝ)*χ)*
        (P.fixed.accuracy j*(((S.levelA qindex).1 : ℝ)+((S.levelB qindex).1 : ℝ)+(m : ℝ))*(m : ℝ)) := by
      apply hleft.trans_eq
      push_cast
      ring
    _ ≤ (4096*((4*D+30)*Real.log (m : ℝ))*χ)*
        (3072*familyRowCoefficient D c*((m : ℝ)^2/Real.sqrt (m/N : ℝ))*(Real.log (m : ℝ))^3) := hprod
    _ = _ := by unfold familyFineLeafCoefficient; ring


theorem PreparedFamilyProblem.absolute_factor_action_uniform_bound
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (C : MainSupportData (mainSketchProgram P.fixed g).eval) (b : ℕ) (hbWidth : b ≤ 2*width (1/2) m) :
    (mainFactorActionCost kernels P.fixed (mainSketchProgram P.fixed g).eval C b P.depth : ℝ) ≤
      familyActionWorkScale I P D c χ := by
  let S := (mainSketchProgram P.fixed g).eval
  let s := Real.sqrt (m/N : ℝ)
  let ell := Real.log (m : ℝ)
  let a := 2*familyActionCostConstant D*ell^2
  let M := familyActionLeafCoefficient D c*χ*((m : ℝ)^2/s)*ell^4
  have hχ0 : 0 ≤ χ := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr I.ratio_positive
  have hfine : 0 ≤ familyFineLeafCoefficient D c := by
    unfold familyFineLeafCoefficient
    have hh := familyRowCoefficient_ge_one D c (by linarith) hc
    positivity
  have hB : 100 ≤ familyActionLeafCoefficient D c := by unfold familyActionLeafCoefficient; linarith
  have hmag := P.scaled_square_ge I hL χ hχ hmLog
  have hbase : P.fixed.accuracy 0*((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M := by
    have hk := mainSupport_dimension_le S C
    have hkernel := hrow.forward C.pair.dimension C.pair.dimension b hk hbWidth
    have hkR : (C.pair.dimension : ℝ) ≤ m := by exact_mod_cast hk
    have hkernel' : ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ 16*χ*(m : ℝ)^2 := by
      push_cast at hkernel
      have hh := mul_le_mul_of_nonneg_left hkR (show 0 ≤ 8*χ*(m : ℝ) by positivity)
      nlinarith
    have hH : P.fixed.accuracy 0 ≤ 1 := by linarith [P.accuracy_le_initial I hL 0 (Nat.zero_le _)]
    have hweighted := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (kernels C.pair.dimension C.pair.dimension b).cost)
    have h16 := mul_le_mul_of_nonneg_left hmag (by norm_num : (0 : ℝ) ≤ 16)
    have hBM := mul_le_mul_of_nonneg_right (show (16 : ℝ) ≤ familyActionLeafCoefficient D c by linarith)
      (show 0 ≤ χ*((m : ℝ)^2/s)*ell^4 by positivity)
    dsimp [M,s,ell] at hBM ⊢
    nlinarith
  have hleaf : ∀ j < P.depth, P.fixed.accuracy j*
      ((mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1) ≤ M := by
    intro j hj
    have hh := P.absolute_weighted_fine_action_bound I hL kernels χ hχ hrow D c hD hc hm hmLog hscale hδ g C b hbWidth j hj
    apply hh.trans
    have hcoeff : familyFineLeafCoefficient D c ≤ familyActionLeafCoefficient D c := by
      unfold familyActionLeafCoefficient
      linarith
    have hp := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ χ*((m : ℝ)^2/s)*ell^4 by positivity)
    convert hp using 1 <;> dsimp [M,s,ell] <;> ring
  have hu := P.factor_action_cost_unfold I hL kernels S C D hD hmLog hscale b
  have hsum : (∑ j ∈ Finset.range P.depth, P.fixed.accuracy j*
      ((mainFineActionCost kernels P.fixed S C j b : ℝ)+(C.pair.dimension : ℝ)*b+1)) ≤ (P.depth : ℝ)*M := by
    calc
      _ ≤ ∑ _j ∈ Finset.range P.depth, M := Finset.sum_le_sum (fun j hj => hleaf j (Finset.mem_range.mp hj))
      _ = _ := by simp
  have ha : 0 ≤ a := by
    have hh := familyActionCostConstant_ge_one D hD
    dsimp [a]
    positivity
  have htotal : P.fixed.accuracy P.depth*(mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤
      a^P.depth*((P.depth+1 : ℕ) : ℝ)*M := by
    apply hu.trans
    have hp := mul_le_mul_of_nonneg_left (add_le_add hbase hsum) (pow_nonneg ha P.depth)
    convert hp using 1 <;> dsimp [a] <;> push_cast <;> ring
  have hsH : s ≤ P.fixed.accuracy P.depth := (P.normal_terminal I hL).1
  have hsmall := mul_le_mul_of_nonneg_right hsH
    (Nat.cast_nonneg (mainFactorActionCost kernels P.fixed S C b P.depth))
  have hdivide : (mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤
      (a^P.depth*((P.depth+1 : ℕ) : ℝ)*M)/s :=
    (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hsmall.trans htotal)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast I.core_positive
  have hNs : (0 : ℝ) < N := by exact_mod_cast I.side_positive
  have hsquare : (m : ℝ)^2/s^2 = (N : ℝ)*(m : ℝ) := by
    dsimp only [s]
    rw [Real.sq_sqrt I.ratio_positive.le]
    field_simp
  apply hdivide.trans_eq
  calc
    _ = a^P.depth*((P.depth+1 : ℕ) : ℝ)*familyActionLeafCoefficient D c*χ*((m : ℝ)^2/s^2)*ell^4 := by
      dsimp [M]
      ring
    _ = _ := by rw [hsquare]; dsimp only [familyActionWorkScale,a,ell]; ring


theorem PreparedFamilyProblem.absolute_true_action_uniform_bound
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (g : MainRandomTape P.fixed) (C : MainSupportData (mainSketchProgram P.fixed g).eval)
    (b : ℕ) (hbWidth : b ≤ 2*width (1/2) m) :
    (mainTrueActionCost kernels P.fixed (mainSketchProgram P.fixed g).eval C b : ℝ) ≤
      familyActionWorkScale I P D c χ := by
  let S := (mainSketchProgram P.fixed g).eval
  have hcost := storedFinePencilAction_cost_fixed_row_bound kernels χ hχ hrow P.fixed.A P.fixed.Bᵀ
    C.pair.factor C.pair.leftInverseᵀ 0 P.fixed.massAccuracy P.fixed.final_budget.mass_positive
    I.core_positive (mainSupport_dimension_le S C) hbWidth
  change (mainTrueActionCost kernels P.fixed S C b : ℝ) ≤
    2048*(neumannCount P.fixed.massAccuracy P.fixed.final_budget.mass_positive : ℝ)*χ*(N+N+m : ℕ)*(m : ℝ) at hcost
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hcount := P.mass_neumann_count_bound I hL D (hlog2.trans hmLog) hscale
  have hχ0 : 0 ≤ χ := by linarith
  have hrows : ((N+N+m : ℕ) : ℝ) ≤ 3*(N : ℝ) := by
    exact_mod_cast (show N+N+m ≤ 3*N by have hh:=I.core_le_side; omega)
  have hcoef : 6144*(52*D+106) ≤ familyActionLeafCoefficient D c := by
    have hE := familyRowCoefficient_ge_one D c (by linarith) hc
    have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 4096*3072*(4*D+30) by positivity)
    unfold familyActionLeafCoefficient familyFineLeafCoefficient
    nlinarith
  have hsmall : (mainTrueActionCost kernels P.fixed S C b : ℝ) ≤
      6144*(52*D+106)*χ*(N : ℝ)*(m : ℝ)*Real.log (m : ℝ) := by
    calc
      _ ≤ 2048*((52*D+106)*Real.log (m : ℝ))*χ*(N+N+m : ℕ)*(m : ℝ) :=
        hcost.trans (by gcongr)
      _ ≤ 2048*((52*D+106)*Real.log (m : ℝ))*χ*(3*(N : ℝ))*(m : ℝ) := by gcongr
      _ = _ := by ring
  exact hsmall.trans (P.action_scale_lower I χ D c (6144*(52*D+106)) (Real.log (m : ℝ)) hχ hD hc
    hmLog (by linarith) hcoef (le_self_pow₀ hmLog (by norm_num)))


theorem absolute_family_input_kernel_cost_bound (I : FamilyProblem N m r)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ) (hm : 2 ≤ m)
    (a k b : ℕ) (ha : a ≤ N) (hk : k ≤ m) (hbWidth : b ≤ 2*width (1/2) m) :
    ((kernels a k b).cost : ℝ) ≤ 16*χ*(N : ℝ)*(m : ℝ) := by
  have hχ0 : 0 ≤ χ := by linarith
  have hh := hrow.forward a k b hk hbWidth
  have hsize : ((a+m : ℕ) : ℝ) ≤ 2*(N : ℝ) := by
    exact_mod_cast (show a+m ≤ 2*N by have hh:=I.core_le_side; omega)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 8*χ by positivity)) (Nat.cast_nonneg m)
  exact hh.trans (hp.trans_eq (by ring))


theorem PreparedFamilyProblem.absolute_six_action_bounds
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (C : MainSupportData (mainSketchProgram P.fixed g).eval) (b : ℕ) (hbWidth : b ≤ 2*width (1/2) m) (hbCore : b ≤ m) :
    let S := (mainSketchProgram P.fixed g).eval
    let M := familyActionWorkScale I P D c χ
    (mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤ M ∧
      (mainTrueActionCost kernels P.fixed S C b : ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M ∧
      (C.pair.dimension : ℝ)*b ≤ M ∧
      ((kernels N m b).cost : ℝ) ≤ M ∧ ((kernels m C.pair.dimension b).cost : ℝ) ≤ M := by
  intro S M
  have hk := mainSupport_dimension_le S C
  have hB : (16 : ℝ) ≤ familyActionLeafCoefficient D c := by
    have hh := familyRowCoefficient_ge_one D c (by linarith) hc
    have hf : 0 ≤ familyFineLeafCoefficient D c := by unfold familyFineLeafCoefficient; positivity
    unfold familyActionLeafCoefficient
    linarith
  have h16 := P.action_scale_lower I χ D c 16 1 hχ hD hc hmLog (by norm_num) hB (one_le_pow₀ hmLog)
  have h16' : 16*χ*(N : ℝ)*(m : ℝ) ≤ M := by simpa only [mul_one] using h16
  have hkb : (C.pair.dimension : ℝ)*b ≤ 16*χ*(N : ℝ)*(m : ℝ) := by
    have hkR : (C.pair.dimension : ℝ) ≤ m := by exact_mod_cast hk
    have hbR : (b : ℝ) ≤ m := by exact_mod_cast hbCore
    have hprod := mul_le_mul hkR hbR (Nat.cast_nonneg b) (Nat.cast_nonneg m)
    have hNm := mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ N by exact_mod_cast I.core_le_side) (Nat.cast_nonneg m)
    have hχNm := mul_le_mul_of_nonneg_right hχ (show 0 ≤ (N : ℝ)*(m : ℝ) by positivity)
    nlinarith
  exact ⟨P.absolute_factor_action_uniform_bound I hL kernels χ hχ hrow D c hD hc hm hmLog hscale hδ g C b hbWidth,
    P.absolute_true_action_uniform_bound I hL kernels χ hχ hrow D c hD hc hm hmLog hscale g C b hbWidth,
    (absolute_family_input_kernel_cost_bound I kernels χ hχ hrow hm _ _ b (hk.trans I.core_le_side) hk hbWidth).trans h16',
    hkb.trans h16',(absolute_family_input_kernel_cost_bound I kernels χ hχ hrow hm N m b le_rfl le_rfl hbWidth).trans h16',
    (absolute_family_input_kernel_cost_bound I kernels χ hχ hrow hm m _ b I.core_le_side hk hbWidth).trans h16'⟩


/-- The six uniform action bounds depend on an independent attempted
width, rather than on the original family seed's rank. -/
theorem PreparedFamilyProblem.absolute_six_action_bounds_of_rank
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed)
    (C : MainSupportData (mainSketchProgram P.fixed g).eval)
    (R : ℕ) (hR : R ≤ ⌊Real.sqrt (m : ℝ)⌋₊) (b : ℕ) (hb : b ≤ R+1) :
    let S := (mainSketchProgram P.fixed g).eval
    let M := familyActionWorkScale I P D c χ
    (mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤ M ∧
      (mainTrueActionCost kernels P.fixed S C b : ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M ∧
      (C.pair.dimension : ℝ)*b ≤ M ∧
      ((kernels N m b).cost : ℝ) ≤ M ∧ ((kernels m C.pair.dimension b).cost : ℝ) ≤ M := by
  have hw := absolute_family_action_widths hm R b hR hb
  exact P.absolute_six_action_bounds I hL kernels χ hχ hrow D c hD hc hm hmLog hscale hδ g C b hw.1 hw.2

/-- A direct family-seed interface, including independent attempted rank
zero. The same realized tape, sketches and support are retained. -/
theorem AbsoluteFamilyProblem.six_action_bounds
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : 1 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.seed.delta)
    (g : MainRandomTape I.seed.prepared.fixed)
    (C : MainSupportData (mainSketchProgram I.seed.prepared.fixed g).eval)
    (R : ℕ) (hR : R ≤ ⌊Real.sqrt (m : ℝ)⌋₊) (b : ℕ) (hb : b ≤ R+1) :
    let P := I.seed.prepared
    let S := (mainSketchProgram P.fixed g).eval
    let M := familyActionWorkScale I.seed P D c χ
    (mainFactorActionCost kernels P.fixed S C b P.depth : ℝ) ≤ M ∧
      (mainTrueActionCost kernels P.fixed S C b : ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost : ℝ) ≤ M ∧
      (C.pair.dimension : ℝ)*b ≤ M ∧
      ((kernels N m b).cost : ℝ) ≤ M ∧ ((kernels m C.pair.dimension b).cost : ℝ) ≤ M :=
  I.seed.prepared.absolute_six_action_bounds_of_rank I.seed hL kernels χ hχ hrow D c hD hc hm hmLog
    hscale hδ g C R hR b hb

/-- The query degree only uses the support dimension and the seed's
condition/accuracy parameters. Its attempted target may be any s, including 0. -/
theorem PreparedFamilyProblem.absoluteQuery_degree_polylog
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hs : s < C.pair.dimension)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    (absoluteQueryDegree P.fixed S C hs : ℝ) ≤
      familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1 := by
  unfold absoluteQueryDegree
  apply P.krylov_degree_polylog I hL C.pair.dimension (by omega)
    (by exact_mod_cast mainSupport_dimension_le S C) D hD hm hscale

theorem PreparedFamilyProblem.absoluteQuery_degree_le_ceiling
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S) (hs : s < C.pair.dimension)
    (D : ℝ) (hD : 0 ≤ D) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ)) :
    absoluteQueryDegree P.fixed S C hs ≤ familyQueryDegreeCeiling I D := by
  have hq := P.absoluteQuery_degree_polylog I hL S C hs D hD hm hscale
  have hceil := Nat.le_ceil (familyQueryDegreeCoefficient D*((N : ℝ)/m)*(Real.log (m : ℝ))^5+1)
  exact_mod_cast hq.trans hceil

theorem PreparedFamilyProblem.absolute_combined_degree_bounds
    (I : FamilyProblem N m r) (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N P.depth) (C : MainSupportData S)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) :
    (∀ (s : ℕ) (hs : s < C.pair.dimension),
      2*absoluteQueryDegree P.fixed S C hs ≤ familyCombinedDegreeCeiling I D c) ∧
      (∀ hk : 1 ≤ C.pair.dimension, absoluteStrongDegree P.fixed S C hk ≤ familyCombinedDegreeCeiling I D c) := by
  constructor
  · intro s hs
    exact (Nat.mul_le_mul_left 2
      (P.absoluteQuery_degree_le_ceiling I hL S C hs D hD hm hscale)).trans (le_max_left _ _)
  · intro hk
    have he : absoluteStrongDegree P.fixed S C hk=mainStrongDegree P.fixed S C hk := rfl
    rw [he]
    exact (P.mainStrong_degree_le_ceiling I hL S C hk D c hD hc hm hscale hδ).trans (le_max_right _ _)

theorem AbsoluteFamilyProblem.absolute_combined_degree_bounds
    (I : AbsoluteFamilyProblem N m) (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (S : StoredSketches N m N I.seed.prepared.depth) (C : MainSupportData S)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.seed.delta) :
    (∀ (s : ℕ) (hs : s < C.pair.dimension),
      2*absoluteQueryDegree I.seed.prepared.fixed S C hs ≤ familyCombinedDegreeCeiling I.seed D c) ∧
      (∀ hk : 1 ≤ C.pair.dimension,
        absoluteStrongDegree I.seed.prepared.fixed S C hk ≤ familyCombinedDegreeCeiling I.seed D c) :=
  I.seed.prepared.absolute_combined_degree_bounds I.seed hL S C D c hD hc hm hscale hδ

end
end HierarchicalAbsoluteSpectral
