import HierarchicalAbsoluteSpectral.SupportReduction
import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDCost

/-! Counted small-core preprocessing. The large support factors remain
implicit, so this stage does not multiply A or B by a dense full-width factor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {n m p s t : ℕ}

structure CoarseSupportData (H : Matrix (Fin s) (Fin m) ℝ)
    (J : Matrix (Fin t) (Fin m) ℝ) where
  pair : PSDGramPair (Hᵀ*H)
  rightGram : Core pair.dimension
  rightGram_eq : rightGram=pair.factorᵀ*(Jᵀ*J)*pair.factor

def coarseSupportProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ) :
    ArithmeticProgram (CoarseSupportData H J) := do
  let GA ← ((kernels m s m).program Hᵀ H).certify
  have hGA : GA.val=Hᵀ*H := GA.property.trans (ArithmeticKernel.program_eval _ _ _)
  have hGApos : GA.val.PosSemidef := by
    rw [hGA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self H
  let p₀ ← psdGramProgram kernels m GA.val hGApos
  let p := p₀.cast hGA
  let GB ← ((kernels m t m).program Jᵀ J).certify
  let Q₁ ← ((kernels p.dimension m m).program p.factorᵀ GB.val).certify
  let Q ← ((kernels p.dimension m p.dimension).program Q₁.val p.factor).certify
  ArithmeticProgram.pure
    { pair := p
      rightGram := Q.val
      rightGram_eq := by
        simp only [Q.property, Q₁.property, GB.property, ArithmeticKernel.program_eval] }

theorem coarseSupportProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ) :
    (coarseSupportProgram kernels H J).admissible := by
  simp only [coarseSupportProgram, admissible_bind, certify_admissible,
    ArithmeticKernel.program_admissible, psdGramProgram_admissible, admissible_pure, and_self]

theorem CoarseSupportData.rightGram_posSemidef {H : Matrix (Fin s) (Fin m) ℝ}
    {J : Matrix (Fin t) (Fin m) ℝ} (out : CoarseSupportData H J) : out.rightGram.PosSemidef := by
  rw [out.rightGram_eq]
  have he : out.pair.factorᵀ*(Jᵀ*J)*out.pair.factor=
      (J*out.pair.factor)ᵀ*(J*out.pair.factor) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (J*out.pair.factor)

theorem CoarseSupportData.support_exact {H : Matrix (Fin s) (Fin m) ℝ}
    {J : Matrix (Fin t) (Fin m) ℝ} (out : CoarseSupportData H J)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (h : ℝ) (hh : h<1) (hsketch : (1-h) • (Aᵀ*A)≤Hᵀ*H) :
    A*B=supportLeftFactor A H out.pair*supportRightFactor H out.pair B :=
  support_reduction_product A B H out.pair h hh hsketch

theorem CoarseSupportData.rightGram_bounds {H : Matrix (Fin s) (Fin m) ℝ}
    {J : Matrix (Fin t) (Fin m) ℝ} (out : CoarseSupportData H J)
    (B : Matrix (Fin m) (Fin p) ℝ) (h : ℝ)
    (hlo : (1-h) • (B*Bᵀ)≤Jᵀ*J) (hup : Jᵀ*J≤(1+h) • (B*Bᵀ)) :
    (1-h) • (supportRightFactor H out.pair B*(supportRightFactor H out.pair B)ᵀ)≤out.rightGram ∧
    out.rightGram≤(1+h) • (supportRightFactor H out.pair B*(supportRightFactor H out.pair B)ᵀ) := by
  have hl := support_gram_congruence_mono hlo out.pair.factor
  have hu := support_gram_congruence_mono hup out.pair.factor
  have he : out.pair.factorᵀ*(B*Bᵀ)*out.pair.factor=
      supportRightFactor H out.pair B*(supportRightFactor H out.pair B)ᵀ := by
    simp only [supportRightFactor, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simpa only [Matrix.mul_smul, Matrix.smul_mul, ← out.rightGram_eq, he] using And.intro hl hu

end
end HierarchicalAbsoluteSpectral
