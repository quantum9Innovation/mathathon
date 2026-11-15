import PortEnergy
import InverseBridge
import Mathlib.Tactic.Linarith

namespace StructuralDefects

open Matrix GrowingDefects

noncomputable section

variable {ι μ κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ]


def repeatedProfile (v : μ → ℝ) (b : κ → ℝ) : μ × κ → ℝ :=
  fun x => v x.1 * b x.2

def repeatedMotif (C : Matrix κ κ ℝ) : Matrix (μ × κ) (μ × κ) ℝ :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

def portCoupling (L : Matrix ι μ ℝ) (b : κ → ℝ) : Matrix ι (μ × κ) ℝ :=
  fun x y => L x y.1 * b y.2

def attachmentMatrix (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (b : κ → ℝ) : Matrix (ι ⊕ (μ × κ)) (ι ⊕ (μ × κ)) ℝ :=
  Matrix.fromBlocks A (portCoupling L b) (portCoupling L b).transpose (repeatedMotif C)

omit [Fintype μ] [Fintype κ] [DecidableEq κ] in
theorem repeatedMotif_symmetric (C : Matrix κ κ ℝ) (hC : C.transpose = C) :
    (repeatedMotif (μ := μ) C).transpose = repeatedMotif C := by
  ext i j
  by_cases hij : i.1 = j.1
  · simp only [Matrix.transpose_apply, repeatedMotif]
    rw [if_pos hij.symm, if_pos hij]
    exact congrFun (congrFun hC i.2) j.2
  · simp only [Matrix.transpose_apply, repeatedMotif]
    rw [if_neg (Ne.symm hij), if_neg hij]

omit [Fintype ι] [DecidableEq ι] [Fintype μ] [Fintype κ] [DecidableEq κ] in
theorem attachmentMatrix_symmetric (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (b : κ → ℝ) (hA : A.transpose = A) (hC : C.transpose = C) :
    (attachmentMatrix A L C b).transpose = attachmentMatrix A L C b := by
  simp only [attachmentMatrix, Matrix.fromBlocks_transpose, Matrix.transpose_transpose,
    hA, repeatedMotif_symmetric C hC]

omit [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ] in
theorem repeatedProfile_add (v w : μ → ℝ) (b : κ → ℝ) :
    repeatedProfile (v + w) b = repeatedProfile v b + repeatedProfile w b := by
  funext x
  simp [repeatedProfile, add_mul]

omit [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ] in
theorem repeatedProfile_smul (t : ℝ) (v : μ → ℝ) (b : κ → ℝ) :
    repeatedProfile (t • v) b = t • repeatedProfile v b := by
  funext x
  simp [repeatedProfile, mul_assoc]

omit [DecidableEq μ] [DecidableEq κ] in
theorem repeatedProfile_dot (v w : μ → ℝ) (b c : κ → ℝ) :
    repeatedProfile v b ⬝ᵥ repeatedProfile w c = (v ⬝ᵥ w) * (b ⬝ᵥ c) := by
  simp only [dotProduct, repeatedProfile, Fintype.sum_prod_type]
  simp_rw [show ∀ i j, v i * b j * (w i * c j) = (v i * w i) * (b j * c j) by
    intro i j
    ring]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.mul_sum _ _ _).symm

omit [DecidableEq κ] in
theorem repeatedMotif_action (C : Matrix κ κ ℝ) (v : μ → ℝ) (b : κ → ℝ) :
    repeatedMotif C *ᵥ repeatedProfile v b = repeatedProfile v (C *ᵥ b) := by
  funext x
  simp [Matrix.mulVec, dotProduct, repeatedMotif, repeatedProfile,
    Fintype.sum_prod_type, Finset.mul_sum, mul_comm, mul_left_comm]

omit [Fintype ι] [DecidableEq ι] [DecidableEq μ] [DecidableEq κ] in
theorem portCoupling_action (L : Matrix ι μ ℝ) (b c : κ → ℝ) (v : μ → ℝ) :
    portCoupling L b *ᵥ repeatedProfile v c = (b ⬝ᵥ c) • (L *ᵥ v) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, portCoupling, repeatedProfile,
    Fintype.sum_prod_type, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, L x i * b j * (v i * c j) = (b j * c j) * (L x i * v i) by
    intro i j
    ring]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]

omit [DecidableEq ι] [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ] in
theorem portCoupling_transpose_action (L : Matrix ι μ ℝ) (b : κ → ℝ) (x : ι → ℝ) :
    (portCoupling L b).transpose *ᵥ x = repeatedProfile (L.transpose *ᵥ x) b := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, portCoupling, repeatedProfile]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem attachmentMatrix_action (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (b c : κ → ℝ) (x : ι → ℝ) (v : μ → ℝ) :
    attachmentMatrix A L C b *ᵥ Sum.elim x (repeatedProfile v c) =
      Sum.elim (A *ᵥ x + (b ⬝ᵥ c) • (L *ᵥ v))
        (repeatedProfile (L.transpose *ᵥ x) b + repeatedProfile v (C *ᵥ c)) := by
  simp only [attachmentMatrix, Matrix.fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, portCoupling_action, portCoupling_transpose_action,
    repeatedMotif_action]

def physicalLift (R : Matrix ι ι ℝ) (L : Matrix ι μ ℝ) (u : ι → ℝ) (M : κ → ℝ)
    (x : ℝ × (μ → ℝ)) : ι ⊕ (μ × κ) → ℝ :=
  Sum.elim (x.1 • u + R *ᵥ (L *ᵥ x.2)) (repeatedProfile x.2 M)

def residualLift (u : ι → ℝ) (b : κ → ℝ) (x : ℝ × (μ → ℝ)) :
    ι ⊕ (μ × κ) → ℝ := Sum.elim (x.1 • u) (repeatedProfile x.2 b)

def retainedAction (L : Matrix ι μ ℝ) (R : Matrix ι ι ℝ) (u : ι → ℝ) (fInv : ℝ)
    (x : ℝ × (μ → ℝ)) : ℝ × (μ → ℝ) :=
  ((L.transpose *ᵥ u) ⬝ᵥ x.2,
    x.1 • (L.transpose *ᵥ u) + (L.transpose * R * L) *ᵥ x.2 - fInv • x.2)

omit [DecidableEq ι] in
theorem outer_projection_action (u x : ι → ℝ) :
    Matrix.vecMulVec u u *ᵥ x = (u ⬝ᵥ x) • u := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change (u i * u j) * x j = _
  ring

omit [DecidableEq ι] in
theorem centered_lift_orthogonal (R : Matrix ι ι ℝ) (u x : ι → ℝ)
    (hR : R.transpose = R) (hRu : R *ᵥ u = 0) :
    u ⬝ᵥ (R *ᵥ x) = 0 := by
  calc
    u ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ (R *ᵥ u) := by
      simpa only [hR] using dotProduct_transpose_mulVec R u x
    _ = 0 := by rw [hRu, dotProduct_zero]

omit [DecidableEq ι] [DecidableEq μ] [DecidableEq κ] in
theorem physicalLift_residual_pairing (R : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (u : ι → ℝ) (M b : κ → ℝ) (hunit : u ⬝ᵥ u = 1)
    (hR : R.transpose = R) (hRu : R *ᵥ u = 0) (hport : M ⬝ᵥ b = 1)
    (x y : ℝ × (μ → ℝ)) :
    physicalLift R L u M x ⬝ᵥ residualLift u b y = x.1 * y.1 + x.2 ⬝ᵥ y.2 := by
  have ho : (R *ᵥ (L *ᵥ x.2)) ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact centered_lift_orthogonal R u (L *ᵥ x.2) hR hRu
  simp only [physicalLift, residualLift, sumElim_dotProduct_sumElim,
    add_dotProduct, smul_dotProduct, dotProduct_smul, repeatedProfile_dot,
    hunit, hport, ho, smul_eq_mul]
  ring

omit [DecidableEq ι] [DecidableEq μ] [DecidableEq κ] in
theorem physicalLift_gram (R : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (u : ι → ℝ) (M : κ → ℝ) (hunit : u ⬝ᵥ u = 1)
    (hR : R.transpose = R) (hRu : R *ᵥ u = 0) (x y : ℝ × (μ → ℝ)) :
    physicalLift R L u M x ⬝ᵥ physicalLift R L u M y =
      x.1 * y.1 + (M ⬝ᵥ M) * (x.2 ⬝ᵥ y.2) +
        (R *ᵥ (L *ᵥ x.2)) ⬝ᵥ (R *ᵥ (L *ᵥ y.2)) := by
  have hox := centered_lift_orthogonal R u (L *ᵥ x.2) hR hRu
  have hoy := centered_lift_orthogonal R u (L *ᵥ y.2) hR hRu
  have hox' : (R *ᵥ (L *ᵥ x.2)) ⬝ᵥ u = 0 := by
    rw [dotProduct_comm, hox]
  simp only [physicalLift, sumElim_dotProduct_sumElim, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, repeatedProfile_dot, hunit, hoy, hox', smul_eq_mul]
  ring

theorem attachment_lift_action (A R : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (u : ι → ℝ) (b M : κ → ℝ) (d fInv : ℝ)
    (hAu : A *ᵥ u = d • u)
    (hsolve : (d • 1 - A) * R = 1 - Matrix.vecMulVec u u)
    (hport : b ⬝ᵥ M = 1) (hM : (d • 1 - C) *ᵥ M = fInv • b)
    (x : ℝ × (μ → ℝ)) :
    attachmentMatrix A L C b *ᵥ physicalLift R L u M x - d • physicalLift R L u M x =
      residualLift u b (retainedAction L R u fInv x) := by
  have hhost := congrArg (fun D : Matrix ι ι ℝ => D *ᵥ (L *ᵥ x.2)) hsolve
  simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, outer_projection_action] at hhost
  have hpair : u ⬝ᵥ (L *ᵥ x.2) = (L.transpose *ᵥ u) ⬝ᵥ x.2 := by
    rw [dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hM
  rw [physicalLift, attachmentMatrix_action, hport, one_smul]
  funext i
  cases i with
  | inl i =>
    have hh := congrFun hhost i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpair] at hh
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAu, residualLift,
      retainedAction, Sum.elim_inl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  | inr i =>
    have hm := congrFun hM i.2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hm
    simp only [residualLift, retainedAction, Sum.elim_inr, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, repeatedProfile, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_eq_mul]
    have hm2 := congrArg (fun t : ℝ => x.2 i.1 * t) hm
    nlinarith [hm2]

theorem constructed_host_resolvent_contract (A : Matrix ι ι ℝ) (u : ι → ℝ) (d : ℝ)
    [Invertible (regularizedMatrix A (Matrix.vecMulVec u u) d)]
    (hA : A.transpose = A) (hAu : A *ᵥ u = d • u) (hunit : u ⬝ᵥ u = 1) :
    let R := constructedProjectedInverse A (Matrix.vecMulVec u u) d
    (d • 1 - A) * R = 1 - Matrix.vecMulVec u u ∧ R.transpose = R ∧ R *ᵥ u = 0 := by
  dsimp only
  have hAP : A * Matrix.vecMulVec u u = d • Matrix.vecMulVec u u := by
    rw [Matrix.mul_vecMulVec, hAu, Matrix.smul_vecMulVec]
  have hPA : Matrix.vecMulVec u u * A = d • Matrix.vecMulVec u u := by
    have h := congrArg Matrix.transpose hAP
    simpa only [Matrix.transpose_mul, Matrix.transpose_vecMulVec, hA,
      Matrix.transpose_smul] using h
  have hPP : Matrix.vecMulVec u u * Matrix.vecMulVec u u = Matrix.vecMulVec u u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hunit, one_smul]
  have hreg : (regularizedMatrix A (Matrix.vecMulVec u u) d).transpose =
      regularizedMatrix A (Matrix.vecMulVec u u) d := by
    simp only [regularizedMatrix, Matrix.transpose_add, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, hA, Matrix.transpose_vecMulVec]
  have hRu : constructedProjectedInverse A (Matrix.vecMulVec u u) d *ᵥ u = 0 := by
    have hc := (constructed_projected_inverse_centered A (Matrix.vecMulVec u u) d hAP hPA hPP).2
    have hPu : Matrix.vecMulVec u u *ᵥ u = u := by
      rw [outer_projection_action, hunit, one_smul]
    calc
      constructedProjectedInverse A (Matrix.vecMulVec u u) d *ᵥ u =
          constructedProjectedInverse A (Matrix.vecMulVec u u) d *ᵥ
            (Matrix.vecMulVec u u *ᵥ u) := by rw [hPu]
      _ = 0 := by rw [Matrix.mulVec_mulVec, hc, Matrix.zero_mulVec]
  refine ⟨constructed_projected_inverse_left A (Matrix.vecMulVec u u) d hAP hPA hPP, ?_, hRu⟩
  simp only [constructedProjectedInverse, Matrix.transpose_sub, Matrix.invOf_eq_nonsing_inv,
    Matrix.transpose_nonsing_inv, hreg, Matrix.transpose_vecMulVec]

theorem actual_attachment_lift_action (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (u : ι → ℝ) (b : κ → ℝ) (d : ℝ)
    [Invertible (regularizedMatrix A (Matrix.vecMulVec u u) d)]
    [Invertible (d • (1 : Matrix κ κ ℝ) - C)]
    (hA : A.transpose = A) (hAu : A *ᵥ u = d • u) (hunit : u ⬝ᵥ u = 1)
    (hf : portResponse (d • 1 - C) b ≠ 0) (x : ℝ × (μ → ℝ)) :
    let R := constructedProjectedInverse A (Matrix.vecMulVec u u) d
    let M := portProfile (d • 1 - C) b
    attachmentMatrix A L C b *ᵥ physicalLift R L u M x - d • physicalLift R L u M x =
      residualLift u b (retainedAction L R u (portResponse (d • 1 - C) b)⁻¹ x) := by
  exact attachment_lift_action A _ L C u b _ d _ hAu
    (constructed_host_resolvent_contract A u d hA hAu hunit).1
    (portProfile_boundary _ b hf) (portProfile_equation _ b) x

omit [DecidableEq μ] in
theorem actual_attachment_lift_pairing (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (u : ι → ℝ) (b : κ → ℝ) (d : ℝ)
    [Invertible (regularizedMatrix A (Matrix.vecMulVec u u) d)]
    [Invertible (d • (1 : Matrix κ κ ℝ) - C)]
    (hA : A.transpose = A) (hAu : A *ᵥ u = d • u) (hunit : u ⬝ᵥ u = 1)
    (hf : portResponse (d • 1 - C) b ≠ 0) (x y : ℝ × (μ → ℝ)) :
    let R := constructedProjectedInverse A (Matrix.vecMulVec u u) d
    let M := portProfile (d • 1 - C) b
    physicalLift R L u M x ⬝ᵥ residualLift u b y = x.1 * y.1 + x.2 ⬝ᵥ y.2 := by
  have h := constructed_host_resolvent_contract A u d hA hAu hunit
  apply physicalLift_residual_pairing _ L u _ b hunit h.2.1 h.2.2
  rw [dotProduct_comm]
  exact portProfile_boundary _ b hf

omit [DecidableEq μ] in
theorem actual_attachment_lift_gram (A : Matrix ι ι ℝ) (L : Matrix ι μ ℝ)
    (C : Matrix κ κ ℝ) (u : ι → ℝ) (b : κ → ℝ) (d : ℝ)
    [Invertible (regularizedMatrix A (Matrix.vecMulVec u u) d)]
    [Invertible (d • (1 : Matrix κ κ ℝ) - C)]
    (hA : A.transpose = A) (hAu : A *ᵥ u = d • u) (hunit : u ⬝ᵥ u = 1)
    (x y : ℝ × (μ → ℝ)) :
    let R := constructedProjectedInverse A (Matrix.vecMulVec u u) d
    let M := portProfile (d • 1 - C) b
    physicalLift R L u M x ⬝ᵥ physicalLift R L u M y =
      x.1 * y.1 + (M ⬝ᵥ M) * (x.2 ⬝ᵥ y.2) +
        (R *ᵥ (L *ᵥ x.2)) ⬝ᵥ (R *ᵥ (L *ᵥ y.2)) := by
  have h := constructed_host_resolvent_contract A u d hA hAu hunit
  exact physicalLift_gram _ L u _ hunit h.2.1 h.2.2 x y

#print axioms repeatedMotif_symmetric
#print axioms attachmentMatrix_symmetric
#print axioms repeatedProfile_add
#print axioms repeatedProfile_smul
#print axioms repeatedProfile_dot
#print axioms repeatedMotif_action
#print axioms portCoupling_action
#print axioms portCoupling_transpose_action
#print axioms attachmentMatrix_action
#print axioms outer_projection_action
#print axioms centered_lift_orthogonal
#print axioms physicalLift_residual_pairing
#print axioms physicalLift_gram
#print axioms attachment_lift_action
#print axioms constructed_host_resolvent_contract
#print axioms actual_attachment_lift_action
#print axioms actual_attachment_lift_pairing
#print axioms actual_attachment_lift_gram

end

end StructuralDefects
