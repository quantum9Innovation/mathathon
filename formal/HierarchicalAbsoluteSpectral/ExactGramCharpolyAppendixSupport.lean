import HierarchicalAbsoluteSpectral.ExactGramCharpolyCost
import HierarchicalAbsoluteSpectral.SupportProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraSingularInertiaCost
import HierarchicalAbsoluteSpectral.MainStatementsExact

/-!
True-Gram product support for the original comparator. The physical support
is stored as Z=A*T; it is not materialized at full width. The small core is
positive definite on the product support, including the empty support.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped BigOperators

structure ExactGramAppendixSupport {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) where
  dimension : ℕ
  dimension_le : dimension ≤ m
  lift : Matrix (Fin m) (Fin dimension) ℝ
  right : Matrix (Fin dimension) (Fin m) ℝ
  core : Core dimension
  positive : core.PosDef
  orthogonal : (A*lift)ᵀ*(A*lift) = 1
  product : A*B = (A*lift)*(right*B)
  gram : core = (right*B)*(right*B)ᵀ

theorem exactGramAppendix_projection_spans {a b s : ℕ}
    (Y : Matrix (Fin a) (Fin b) ℝ) (Q : Matrix (Fin a) (Fin s) ℝ) (H : Core s)
    (hQ : Qᵀ*Q = 1) (hY : Y*Yᵀ = Q*H*Qᵀ) : Y = Q*(Qᵀ*Y) := by
  let P : Core a := 1-Q*Qᵀ
  have hPQ : P*Q = 0 := by
    simp only [P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ,
      Matrix.mul_one, sub_self]
  have hPK : P*(Y*Yᵀ) = 0 := by
    rw [hY]
    simp only [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
  have hzero : (P*Y)*(P*Y)ᵀ = 0 := by
    calc
      _ = (P*(Y*Yᵀ))*Pᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hPK, Matrix.zero_mul]
  have htr : (P*Y)ᵀ = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hzero)
  have hPY : P*Y = 0 := by
    simpa only [Matrix.transpose_transpose, Matrix.transpose_zero] using congrArg Matrix.transpose htr
  simpa only [P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, sub_eq_zero] using hPY

def exactGramAppendixSupportOfSmall {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (left : PSDGramPair (Aᵀ*A)) (K : Core left.dimension)
    (hK : K = left.factorᵀ*(B*Bᵀ)*left.factor)
    (support : InertiaSupport K)
    (T : Matrix (Fin m) (Fin support.dimension) ℝ)
    (R : Matrix (Fin support.dimension) (Fin m) ℝ)
    (hT : T = left.leftInverseᵀ*support.basis)
    (hR : R = support.basisᵀ*left.factorᵀ) : ExactGramAppendixSupport A B := by
  let Z₀ := A*left.leftInverseᵀ
  let D := left.factorᵀ*B
  have hDD : D*Dᵀ = K := by
    simp only [D, hK, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hKpos : K.PosSemidef := by
    rw [← hDD]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose D
  have hcore : support.compressed.PosSemidef := by
    rw [support.compressed_eq]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hKpos.conjTranspose_mul_mul_same support.basis
  have hcorepos : support.compressed.PosDef := hcore.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr support.compressed_isUnit)
  have hZ₀ : Z₀ᵀ*Z₀ = 1 := (rangeFromPSDGram A left).orthogonal
  have hA : A = Z₀*left.factorᵀ := (rangeFromPSDGram A left).spans
  have hD : D = support.basis*(support.basisᵀ*D) :=
    exactGramAppendix_projection_spans D support.basis support.compressed support.basis_orthogonal
      (hDD.trans support.decomposition)
  refine {
    dimension := support.dimension
    dimension_le := support.dimension_le.trans (by simpa only [Fintype.card_fin] using left.dimension_le)
    lift := T
    right := R
    core := support.compressed
    positive := hcorepos
    orthogonal := ?_
    product := ?_
    gram := ?_ }
  · rw [hT]
    calc
      _ = support.basisᵀ*(Z₀ᵀ*Z₀)*support.basis := by
        simp only [Z₀, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hZ₀, Matrix.mul_one, support.basis_orthogonal]
  · calc
      A*B = Z₀*D := by
        simpa only [D, Matrix.mul_assoc] using congrArg (·*B) hA
      _ = Z₀*(support.basis*(support.basisᵀ*D)) := congrArg (Z₀*·) hD
      _ = (A*T)*(R*B) := by rw [hT,hR]; simp only [Z₀,D,Matrix.mul_assoc]
  · calc
      support.compressed = support.basisᵀ*K*support.basis := support.compressed_eq
      _ = support.basisᵀ*(D*Dᵀ)*support.basis :=
        congrArg (fun M => support.basisᵀ*M*support.basis) hDD.symm
      _ = (R*B)*(R*B)ᵀ := by
        rw [hR]
        simp only [D, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

def exactGramAppendixEmptySupport (D : Core 0) : InertiaSupport D where
  dimension := 0
  nullity := 0
  dimension_le := le_rfl
  total := rfl
  basis := 0
  complement := 0
  basis_orthogonal := Subsingleton.elim _ _
  complement_orthogonal := Subsingleton.elim _ _
  cross_zero := Subsingleton.elim _ _
  projectors := Subsingleton.elim _ _
  compressed := 0
  compressed_eq := Subsingleton.elim _ _
  compressed_isUnit := by simp
  decomposition := Subsingleton.elim _ _

def exactGramAppendixSupportCompressionProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    (k : ℕ) → (D : Core k) → Dᵀ = D → ArithmeticProgram (InertiaSupport D)
  | 0, D, _ => ArithmeticProgram.pure (exactGramAppendixEmptySupport D)
  | k+1, D, hD => inertiaSupportProgram kernels D hD

theorem exactGramAppendixSupportCompressionProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (k : ℕ) (D : Core k) (hD : Dᵀ = D) :
    (exactGramAppendixSupportCompressionProgram kernels k D hD).admissible := by
  cases k
  · trivial
  · exact inertiaSupportProgram_admissible kernels D hD

def exactGramAppendixSupportProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    ArithmeticProgram (ExactGramAppendixSupport A B) := do
  let GA ← certify ((kernels m n m).program Aᵀ A)
  have hGA : GA.val = Aᵀ*A := GA.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hGApos : GA.val.PosSemidef := by
    rw [hGA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  let left₀ ← psdGramProgram kernels m GA.val hGApos
  let left := left₀.cast hGA
  let GB ← certify ((kernels m p m).program B Bᵀ)
  let K₁ ← certify ((kernels left.dimension m m).program left.factorᵀ GB.val)
  let K ← certify ((kernels left.dimension m left.dimension).program K₁.val left.factor)
  have hK : K.val = left.factorᵀ*(B*Bᵀ)*left.factor := by
    rw [K.property, ArithmeticKernel.program_eval, K₁.property, ArithmeticKernel.program_eval,
      GB.property, ArithmeticKernel.program_eval]
  have hKpos : K.val.PosSemidef := by
    rw [hK]
    have hGBpos : (B*Bᵀ).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose B
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hGBpos.conjTranspose_mul_mul_same left.factor
  have hKsym : K.valᵀ = K.val := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hKpos.isHermitian.eq
  let support ← exactGramAppendixSupportCompressionProgram kernels left.dimension K.val hKsym
  let T ← certify ((kernels m left.dimension support.dimension).program left.leftInverseᵀ support.basis)
  let R ← certify ((kernels support.dimension left.dimension m).program support.basisᵀ left.factorᵀ)
  ArithmeticProgram.pure (exactGramAppendixSupportOfSmall A B left K.val hK support T.val R.val
    (T.property.trans (ArithmeticKernel.program_eval _ _ _))
    (R.property.trans (ArithmeticKernel.program_eval _ _ _)))

theorem exactGramAppendixSupportProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (exactGramAppendixSupportProgram kernels A B).admissible := by
  simp only [exactGramAppendixSupportProgram, admissible_bind, certify_admissible,
    ArithmeticKernel.program_admissible, psdGramProgram_admissible,
    exactGramAppendixSupportCompressionProgram_admissible, admissible_pure, and_self]

namespace ExactGramAppendixSupport

variable {n m p : ℕ} {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin p) ℝ}

theorem covariance (out : ExactGramAppendixSupport A B) :
    (A*B)*(A*B)ᵀ = (A*out.lift)*out.core*(A*out.lift)ᵀ := by
  rw [out.product, out.gram]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

def action (out : ExactGramAppendixSupport A B)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (w : ℕ) : MatrixAction (A*out.lift) w :=
  ((kernels n m w).action A).comp ((kernels m out.dimension w).action out.lift)

def exactOutputProgram (out : ExactGramAppendixSupport A B)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (r : ℕ) (hr : out.dimension ≤ r) :
    ArithmeticProgram (FixedRankOutput n p r) :=
  supportExactOutputProgram kernels A B (out.action kernels out.dimension) hr

theorem exactOutputProgram_exact (out : ExactGramAppendixSupport A B)
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (r : ℕ) (hr : out.dimension ≤ r) :
    (out.exactOutputProgram kernels r hr).eval.product = A*B :=
  supportExactOutputProgram_exact kernels A B (A*out.lift) (out.right*B) out.product
    (out.action kernels out.dimension) hr

end ExactGramAppendixSupport

end
end HierarchicalAbsoluteSpectral
