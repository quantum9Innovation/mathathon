import HierarchicalAbsoluteSpectral.CoarseAlgebraRange
import HierarchicalAbsoluteSpectral.MatrixInequalities

/-! Exact support and controlled normalization from a coarse sketch Gram.
The basis is stored implicitly as A times a computed small right factor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {n m p s : ℕ}

theorem support_gram_congruence_mono {a b : ℕ} {A B : Core a} (hAB : A≤B)
    (R : Matrix (Fin a) (Fin b) ℝ) : Rᵀ*A*R≤Rᵀ*B*R := by
  have h := (show (B-A).PosSemidef from hAB).conjTranspose_mul_mul_same R
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.le_iff] using h

def supportLeftFactor (A : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin s) (Fin m) ℝ) (P : PSDGramPair (Hᵀ*H)) :
    Matrix (Fin n) (Fin P.dimension) ℝ := A*P.leftInverseᵀ

def supportRightFactor (H : Matrix (Fin s) (Fin m) ℝ) (P : PSDGramPair (Hᵀ*H))
    (B : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin P.dimension) (Fin p) ℝ := P.factorᵀ*B

theorem support_reduction_exact (A : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin s) (Fin m) ℝ) (P : PSDGramPair (Hᵀ*H))
    (h : ℝ) (hh : h<1) (hsketch : (1-h) • (Aᵀ*A)≤Hᵀ*H) :
    A=supportLeftFactor A H P*P.factorᵀ := by
  let E : Core m := 1-P.leftInverseᵀ*P.factorᵀ
  have hr := (rangeFromPSDGram H P).spans
  change H=(H*P.leftInverseᵀ)*P.factorᵀ at hr
  have hHE : H*E=0 := by
    dsimp only [E]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← hr, sub_self]
  have hc := star_left_conjugate_le_conjugate hsketch E
  have hGr : (A*E)ᵀ*(A*E)=Eᵀ*(Aᵀ*A)*E := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hGH : Eᵀ*(Hᵀ*H)*E=0 := by
    calc
      _ = (H*E)ᵀ*(H*E) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hHE]; simp
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_smul, Matrix.smul_mul, hGH, ← hGr] at hc
  have hp : (0 : Core m)≤(A*E)ᵀ*(A*E) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (A*E)).nonneg
  have hz : (1-h) • ((A*E)ᵀ*(A*E))=0 :=
    le_antisymm hc (smul_nonneg (by linarith) hp)
  have hAE : A*E=0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (smul_eq_zero.mp hz).resolve_left (by linarith)
  simpa only [E, Matrix.mul_sub, Matrix.mul_one, supportLeftFactor, Matrix.mul_assoc,
    sub_eq_zero] using hAE

theorem support_reduction_product (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (H : Matrix (Fin s) (Fin m) ℝ)
    (P : PSDGramPair (Hᵀ*H)) (h : ℝ) (hh : h<1)
    (hsketch : (1-h) • (Aᵀ*A)≤Hᵀ*H) :
    A*B=supportLeftFactor A H P*supportRightFactor H P B := by
  calc
    A*B=(supportLeftFactor A H P*P.factorᵀ)*B :=
      congrArg (·*B) (support_reduction_exact A H P h hh hsketch)
    _ = _ := by simp only [supportRightFactor, Matrix.mul_assoc]

theorem support_normalized_gram (A : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin s) (Fin m) ℝ) (P : PSDGramPair (Hᵀ*H))
    (h : ℝ) (hh : 0≤h) (hh' : h<1)
    (hlo : (1-h) • (Aᵀ*A)≤Hᵀ*H) (hup : Hᵀ*H≤(1+h) • (Aᵀ*A)) :
    (1/(1+h)) • (1 : Core P.dimension)≤
      (supportLeftFactor A H P)ᵀ*supportLeftFactor A H P ∧
    (supportLeftFactor A H P)ᵀ*supportLeftFactor A H P≤
      (1/(1-h)) • (1 : Core P.dimension) := by
  have hunit : P.leftInverse*(Hᵀ*H)*P.leftInverseᵀ=1 := by
    calc
      _ = (H*P.leftInverseᵀ)ᵀ*(H*P.leftInverseᵀ) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := (rangeFromPSDGram H P).orthogonal
  have hGram : P.leftInverse*(Aᵀ*A)*P.leftInverseᵀ=
      (supportLeftFactor A H P)ᵀ*supportLeftFactor A H P := by
    simp only [supportLeftFactor, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hl := support_gram_congruence_mono hlo P.leftInverseᵀ
  have hu := support_gram_congruence_mono hup P.leftInverseᵀ
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, hunit, hGram] at hl hu
  constructor
  · have hs := smul_le_smul_of_nonneg_left hu (by positivity : 0≤1/(1+h))
    convert hs using 1
    rw [smul_smul]
    have hc : (1/(1+h))*(1+h)=1 := by field_simp [(by positivity : (1:ℝ)+h≠0)]
    rw [hc, one_smul]
  · have hs := smul_le_smul_of_nonneg_left hl (by positivity : 0≤1/(1-h))
    convert hs using 1
    rw [smul_smul]
    have hc : (1/(1-h))*(1-h)=1 := by field_simp [(by linarith : (1:ℝ)-h≠0)]
    rw [hc, one_smul]

end
end HierarchicalAbsoluteSpectral
