import HierarchicalAbsoluteSpectral.MainOperatorProgram
import HierarchicalAbsoluteSpectral.ProbabilityInitializerProgram

/-! Every tolerance and data-dependent loop length used by the main
algorithm is computed by field operations and comparisons. Certificates
only identify the values produced by those operations. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def certifyAs {α : Type} (p : ArithmeticProgram α) (x : α) (h : p.eval=x) :
    ArithmeticProgram {y : α // y=x} := do
  let v ← p.certify
  ArithmeticProgram.pure ⟨v.val,v.property.trans h⟩

@[simp] theorem certifyAs_eval {α : Type} (p : ArithmeticProgram α) (x : α) (h : p.eval=x) :
    (certifyAs p x h).eval = ⟨x,rfl⟩ := by
  apply Subtype.ext
  simp [certifyAs, h]

@[simp] theorem certifyAs_work {α : Type} (p : ArithmeticProgram α) (x : α) (h : p.eval=x) :
    (certifyAs p x h).work = p.work := by simp [certifyAs]

@[simp] theorem certifyAs_admissible {α : Type} (p : ArithmeticProgram α) (x : α) (h : p.eval=x) :
    (certifyAs p x h).admissible ↔ p.admissible := by simp [certifyAs]

def hierarchyConstantProgram : ℕ → ArithmeticProgram ℝ
  | 0 => .pure 36
  | j+1 => do
      let c ← hierarchyConstantProgram j
      let d ← add c 1
      mul 100 d

@[simp] theorem hierarchyConstantProgram_eval (j : ℕ) :
    (hierarchyConstantProgram j).eval=hierarchyConstant j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [hierarchyConstantProgram,hierarchyConstant,ih]

@[simp] theorem hierarchyConstantProgram_work (j : ℕ) :
    (hierarchyConstantProgram j).work=2*j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [hierarchyConstantProgram,ih]; omega

theorem hierarchyConstantProgram_admissible (j : ℕ) :
    (hierarchyConstantProgram j).admissible := by
  induction j with
  | zero => trivial
  | succ j ih => simp [hierarchyConstantProgram,ih]

def finalAlphaProgram (C h θ : ℝ) : ArithmeticProgram ℝ := do
  let a ← add C 1
  let b ← mul 1000000 a
  let c ← mul b h
  div θ c

@[simp] theorem finalAlphaProgram_eval (C h θ : ℝ) :
    (finalAlphaProgram C h θ).eval=literalFinalAlpha C h θ := by
  simp [finalAlphaProgram,literalFinalAlpha]

@[simp] theorem finalAlphaProgram_work (C h θ : ℝ) :
    (finalAlphaProgram C h θ).work=4 := by simp [finalAlphaProgram]

theorem finalAlphaProgram_admissible (C h θ : ℝ) (hC : 1 ≤ C) (hh : 0 < h) :
    (finalAlphaProgram C h θ).admissible := by
  have hp : 0 < 1000000*(C+1)*h := by positivity
  simpa [finalAlphaProgram] using hp.ne'

def finalMassProgram (C θ : ℝ) : ArithmeticProgram ℝ := do
  let a ← add C 1
  let b ← mul 1000000 a
  div θ b

@[simp] theorem finalMassProgram_eval (C θ : ℝ) :
    (finalMassProgram C θ).eval=literalFinalMass C θ := by simp [finalMassProgram,literalFinalMass]

@[simp] theorem finalMassProgram_work (C θ : ℝ) :
    (finalMassProgram C θ).work=3 := by simp [finalMassProgram]

theorem finalMassProgram_admissible (C θ : ℝ) (hC : 1 ≤ C) :
    (finalMassProgram C θ).admissible := by
  have hp : 0 < 1000000*(C+1) := by positivity
  simpa [finalMassProgram] using hp.ne'

def finalNearProgram (C α h : ℝ) : ArithmeticProgram ℝ := do
  let a ← mul 4 C
  let b ← mul a α
  mul b h

@[simp] theorem finalNearProgram_eval (C α h : ℝ) :
    (finalNearProgram C α h).eval=4*C*α*h := by simp [finalNearProgram]
@[simp] theorem finalNearProgram_work (C α h : ℝ) :
    (finalNearProgram C α h).work=3 := by simp [finalNearProgram]
theorem finalNearProgram_admissible (C α h : ℝ) :
    (finalNearProgram C α h).admissible := by simp [finalNearProgram]

def allocatedFailureProgram (δ count : ℝ) : ArithmeticProgram ℝ := do
  let a ← add count 1
  let b ← mul 20 a
  div δ b

@[simp] theorem allocatedFailureProgram_eval (δ count : ℝ) :
    (allocatedFailureProgram δ count).eval=δ/(20*(count+1)) := by simp [allocatedFailureProgram]
@[simp] theorem allocatedFailureProgram_work (δ count : ℝ) :
    (allocatedFailureProgram δ count).work=3 := by simp [allocatedFailureProgram]
theorem allocatedFailureProgram_admissible (δ count : ℝ) (hc : 0 ≤ count) :
    (allocatedFailureProgram δ count).admissible := by
  have hp : 0 < 20*(count+1) := by positivity
  simpa [allocatedFailureProgram] using hp.ne'

structure PreparedMainScalars (I : FixedProblem n m p r L) where
  alpha : {v : ℝ // v=I.alpha}
  mass : {v : ℝ // v=I.massAccuracy}
  near : {v : ℝ // v=I.nearTolerance}
  singleFailure : {v : ℝ // v=I.singleFailure}
  sketchFailure : {v : ℝ // v=I.sketchFailure}
  queryFailure : {v : ℝ // v=I.queryFailure}
  ratios : {v : Fin (L+1) → ℝ // v=fun j => safeAccuracy I (j.val+1)/safeAccuracy I j.val}
  fineMass : {v : Fin (L+1) → ℝ // v=fun j => safeAccuracy I j.val/100}
  cap : {v : ℕ // v=I.queryCap}
  repetitions : {v : ℕ // v=I.repetitions}

def canonicalMainScalars (I : FixedProblem n m p r L) : PreparedMainScalars I where
  alpha := ⟨_,rfl⟩
  mass := ⟨_,rfl⟩
  near := ⟨_,rfl⟩
  singleFailure := ⟨_,rfl⟩
  sketchFailure := ⟨_,rfl⟩
  queryFailure := ⟨_,rfl⟩
  ratios := ⟨_,rfl⟩
  fineMass := ⟨_,rfl⟩
  cap := ⟨_,rfl⟩
  repetitions := ⟨_,rfl⟩

theorem PreparedMainScalars.eq_canonical (I : FixedProblem n m p r L) (P : PreparedMainScalars I) :
    P=canonicalMainScalars I := by
  have h {α : Type} (x : α) (a : {v : α // v=x}) : a=⟨x,rfl⟩ := Subtype.ext a.property
  cases P
  simp only [canonicalMainScalars,h]

def mainScalarProgram (I : FixedProblem n m p r L) : ArithmeticProgram (PreparedMainScalars I) := do
  let c ← certifyAs (hierarchyConstantProgram L) (hierarchyConstant L) (hierarchyConstantProgram_eval L)
  let a ← certifyAs (finalAlphaProgram c.val (I.accuracy L) I.theta) I.alpha (by
    rw [finalAlphaProgram_eval,c.property]; rfl)
  let e ← certifyAs (finalMassProgram c.val I.theta) I.massAccuracy (by
    rw [finalMassProgram_eval,c.property]; rfl)
  let x ← certifyAs (finalNearProgram c.val a.val (I.accuracy L)) I.nearTolerance (by
    rw [finalNearProgram_eval,c.property,a.property]; rfl)
  let β ← certifyAs (div I.delta 20) I.singleFailure rfl
  let βs ← certifyAs (allocatedFailureProgram I.delta (L : ℝ)) I.sketchFailure rfl
  let ratios ← certifyAs (tabulate (L+1) (fun j => div (safeAccuracy I (j.val+1)) (safeAccuracy I j.val)))
    (fun j => safeAccuracy I (j.val+1)/safeAccuracy I j.val) (by simp)
  let masses ← certifyAs (tabulate (L+1) (fun j => div (safeAccuracy I j.val) 100))
    (fun j => safeAccuracy I j.val/100) (by simp)
  let ratio ← (initializerRatioProgram m β.val).certify
  let budget ← (mul 16 ratio.val).certify
  have hb : budget.val=16*initializerRatio m I.singleFailure := by
    rw [budget.property,eval_mul,ratio.property,initializerRatioProgram_eval,β.property]
  have hx : 0 < x.val := by rw [x.property]; exact I.nearTolerance_positive
  let cap ← certifyAs (scalarHalving budget.val x.val hx) I.queryCap (by
    rw [(scalarHalving_checked _ _ hx).1,hb]
    simp only [x.property]
    rfl)
  let capReal ← (scalarNatProgram cap.val).certify
  let βq ← certifyAs (allocatedFailureProgram I.delta capReal.val) I.queryFailure (by
    rw [allocatedFailureProgram_eval,capReal.property,(scalarNatProgram_specification _).1,cap.property]
    rfl)
  have hq : 0 < βq.val := by rw [βq.property]; exact I.queryFailure_positive
  let repetitions ← certifyAs (scalarHalving 1 βq.val hq) I.repetitions (by
    rw [(scalarHalving_checked _ _ hq).1]
    simp only [βq.property]
    rfl)
  ArithmeticProgram.pure
    { alpha := a, mass := e, near := x, singleFailure := β, sketchFailure := βs,
      queryFailure := βq, ratios := ratios, fineMass := masses, cap := cap, repetitions := repetitions }

theorem mainScalarProgram_eval (I : FixedProblem n m p r L) :
    (mainScalarProgram I).eval=canonicalMainScalars I :=
  PreparedMainScalars.eq_canonical I _

theorem mainScalarProgram_admissible (I : FixedProblem n m p r L) :
    (mainScalarProgram I).admissible := by
  have hβ : I.singleFailure ≠ 0 :=
    (div_pos I.delta_positive (by norm_num : (0 : ℝ) < 20)).ne'
  unfold mainScalarProgram
  simp only [admissible_bind,certifyAs_admissible,certifyAs_eval,hierarchyConstantProgram_admissible,
    finalAlphaProgram_admissible _ _ _ (hierarchyConstant_ge_one L) (I.accuracy_positive L le_rfl),
    finalMassProgram_admissible _ _ (hierarchyConstant_ge_one L),finalNearProgram_admissible,
    admissible_div,allocatedFailureProgram_admissible _ _ (Nat.cast_nonneg L),
    admissible_tabulate,certify_admissible,initializerRatioProgram_admissible m I.singleFailure hβ,
    admissible_mul,
    (scalarHalving_checked _ _ _).2.2,(scalarNatProgram_specification _).2.2,
    admissible_pure,true_and,and_true]
  refine ⟨by norm_num,?_,by norm_num,?_⟩
  · intro j
    exact (safeAccuracy_pos I j.val).ne'
  · apply allocatedFailureProgram_admissible
    rw [certify_eval,(scalarNatProgram_specification _).1]
    positivity

theorem mainScalarProgram_work (I : FixedProblem n m p r L) :
    (mainScalarProgram I).work = 4*L+3*I.queryCap+2*I.repetitions+29 := by
  have halving_eval (x ε : ℝ) (hε : 0 < ε) := (scalarHalving_checked x ε hε).1
  have halving_work (x ε : ℝ) (hε : 0 < ε) := (scalarHalving_checked x ε hε).2.1
  have nat_eval (j : ℕ) := (scalarNatProgram_specification j).1
  have nat_work (j : ℕ) := (scalarNatProgram_specification j).2.1
  simp only [mainScalarProgram,work_bind,certifyAs_work,certifyAs_eval,
    hierarchyConstantProgram_work,finalAlphaProgram_work,finalMassProgram_work,
    finalNearProgram_work,work_div,allocatedFailureProgram_work,work_tabulate,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    certify_work,initializerRatioProgram_work,work_mul,halving_work,nat_work,
    certify_eval,eval_mul,initializerRatioProgram_eval,nat_eval,halving_eval,
    work_pure,add_zero]
  simp only [FixedProblem.queryCap,FixedProblem.repetitions]
  omega

end
end HierarchicalAbsoluteSpectral
