import HierarchicalAbsoluteSpectral.ThresholdQueryAutomatic
import HierarchicalAbsoluteSpectral.BaseColumnBlocks

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped BigOperators
variable {k b : ℕ}

theorem krylovRangeProgram_work_real
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (P : MatrixAction T b) (q : ℕ) (Ω : Matrix (Fin k) (Fin b) ℝ)
    (R : ℝ) (hR : ∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) :
    ((krylovRangeProgram kernels T P q Ω).work:ℝ) ≤ (q:ℝ)*P.cost+R := by
  have hb : ((krylovBlocksProgram P.program q Ω).work:ℝ) ≤ (q:ℝ)*P.cost := by
    exact_mod_cast krylovBlocksProgram_work_le P.program P.cost P.work_le q Ω
  simp only [krylovRangeProgram,work_bind,certify_work,work_pure,add_zero,Nat.cast_add]
  exact add_le_add hb (hR _)

theorem columnBlocks_krylovQueryDataProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (P : MatrixAction T b) (hb : 0 < b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin b) ℝ) (hk : 1 ≤ k)
    (R : ℝ) (hR : ∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) :
    ((krylovQueryDataProgram kernels T hT (fun w => P.columnBlocks hb w) q Ω).work:ℝ) ≤
      (3*q+2:ℕ)*P.cost+R+kernelEnvelope kernels k := by
  let actions := fun w => P.columnBlocks hb w
  let out := (krylovRangeProgram kernels T (actions b) q Ω).eval
  have hdim : out.dimension ≤ k := out.dimension_le_rows
  have hdimW : out.dimension ≤ (q+1)*b := out.dimension_le_cols
  have hbase : (actions b).cost ≤ 2*P.cost := by
    apply (P.columnBlocks_cost_le hb b).trans
    rw [Nat.div_self hb]
  have hwide : (actions out.dimension).cost ≤ (q+2)*P.cost := by
    apply (P.columnBlocks_cost_le hb out.dimension).trans
    apply Nat.mul_le_mul_right
    have hh := Nat.div_le_div_right (c := b) hdimW
    rw [Nat.mul_div_cancel _ hb] at hh
    omega
  have hrange := krylovRangeProgram_work_real kernels T (actions b) q Ω R hR
  have hquery : ((krylovQueryDataProgram kernels T hT actions q Ω).work:ℝ) ≤
      (krylovRangeProgram kernels T (actions b) q Ω).work+
        (actions out.dimension).cost+(kernels out.dimension k out.dimension).cost := by
    exact_mod_cast krylovQueryDataProgram_work_le kernels T hT actions q Ω
  have hkernel : ((kernels out.dimension k out.dimension).cost:ℝ) ≤ kernelEnvelope kernels k := by
    exact_mod_cast kernelEnvelope_le kernels k out.dimension k out.dimension hdim le_rfl hdim (by omega)
  have hbaseR : ((actions b).cost:ℝ) ≤ 2*P.cost := by exact_mod_cast hbase
  have hwideR : ((actions out.dimension).cost:ℝ) ≤ (q+2:ℕ)*P.cost := by exact_mod_cast hwide
  push_cast at hbaseR hwideR ⊢
  nlinarith

theorem columnBlocks_krylovFullMatrixProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (P : MatrixAction T b) (hb : 0 < b)
    (q : ℕ) (Ω : Matrix (Fin k) (Fin b) ℝ) (hk : 1 ≤ k)
    (R : ℝ) (hR : ∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) :
    ((krylovFullMatrixProgram kernels T hT (fun w => P.columnBlocks hb w) q Ω).work:ℝ) ≤
      (3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k := by
  let actions := fun w => P.columnBlocks hb w
  let out := (krylovQueryDataProgram kernels T hT actions q Ω).eval
  have hw : out.range.dimension ≤ k := out.range.dimension_le_rows
  have h1 : ((kernels k out.range.dimension out.range.dimension).cost:ℝ) ≤ kernelEnvelope kernels k := by
    exact_mod_cast kernelEnvelope_le kernels k k out.range.dimension out.range.dimension le_rfl hw hw (by omega)
  have h2 : ((kernels k out.range.dimension k).cost:ℝ) ≤ kernelEnvelope kernels k := by
    exact_mod_cast kernelEnvelope_le kernels k k out.range.dimension k le_rfl hw le_rfl (by omega)
  have hc := columnBlocks_krylovQueryDataProgram_work_bound kernels T hT P hb q Ω hk R hR
  rw [krylovFullMatrixProgram_work,Nat.cast_add,Nat.cast_add]
  change ((krylovQueryDataProgram kernels T hT actions q Ω).work:ℝ)+
    ((kernels k out.range.dimension out.range.dimension).cost:ℝ)+(kernels k out.range.dimension k).cost ≤ _
  linarith

theorem columnBlocks_gaussianKrylovRitzTestsProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (T : Core k) (hT : T.IsHermitian) (P : MatrixAction T b) (hb : 0 < b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ b)
    (G : Fin b → Fin k → ℝ) (j : Fin k) (ε : ℝ) (g : Fin 2 → Fin (k*k) → ℝ)
    (R : ℝ) (hR : ∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) :
    ((gaussianKrylovRitzTestsProgram kernels T hT (fun w => P.columnBlocks hb w)
      q S source G j ε g).work:ℝ) ≤
      source.cost+(3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k+212*(C+1)*(k:ℝ)^p := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  let actions := fun w => P.columnBlocks hb w
  let M := (gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).eval
  have hM : M.val.IsHermitian := by
    rw [M.property]
    exact krylovRitzFixedMatrix_isHermitian kernels T hT q (Sᵀ*columnsMatrix G)
  have hi := fixedRitzTestsProgram_work_bound kernels C p hC hp hK M.val hM j ε hk g
  have hs : ((source.program (columnsMatrix G)).work:ℝ) ≤ source.cost := by exact_mod_cast source.work_le _
  have hm := columnBlocks_krylovFullMatrixProgram_work_bound kernels T hT P hb q
    (source.program (columnsMatrix G)).certify.eval.val hk R hR
  have hfull : ((gaussianKrylovFullMatrixProgram kernels T hT actions q S source G).work:ℝ) ≤
      source.cost+(3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k := by
    simp only [gaussianKrylovFullMatrixProgram,work_bind,certify_work,work_pure,add_zero,Nat.cast_add]
    push_cast at hm ⊢
    linarith
  simp only [gaussianKrylovRitzTestsProgram,work_bind,Nat.cast_add]
  split <;> simp only [work_pure,Nat.cast_zero,add_zero] <;>
    simpa only [Nat.cast_add] using add_le_add hfull hi

theorem columnBlocks_repeatedKrylovQueryProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (T : Core k) (hT : T.IsHermitian) (P : MatrixAction T b) (hb : 0 < b)
    (q : ℕ) (S : Core k) (source : MatrixAction Sᵀ b)
    (j : Fin k) (ε : ℝ) (N : ℕ)
    (G : Fin N → Fin b → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ)
    (R : ℝ) (hR : ∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ,
      ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) :
    ((repeatedKrylovQueryProgram kernels T hT (fun w => P.columnBlocks hb w)
      q S source j ε N G g).work:ℝ) ≤
      (N:ℝ)*(source.cost+(3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k+212*(C+1)*(k:ℝ)^p) := by
  rw [repeatedKrylovQueryProgram_work,Nat.cast_sum]
  calc
    _ ≤ ∑ _i : Fin N,
        ((source.cost:ℝ)+(3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k+212*(C+1)*(k:ℝ)^p) := by
      apply Finset.sum_le_sum
      intro i hi
      exact columnBlocks_gaussianKrylovRitzTestsProgram_work_bound kernels C p hC hp hK
        T hT P hb q S source (G i) j ε (g i) R hR
    _ = _ := by simp; ring

theorem columnBlocks_automaticKrylovQueryProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (T : Core k) (hT : T.IsHermitian) (P : MatrixAction T b) (hb : 0 < b)
    (S : Core k) (source : MatrixAction Sᵀ b) (j : Fin k) (U ε : ℝ)
    (hk : 1 ≤ k) (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (N : ℕ) (G : Fin N → Fin b → Fin k → ℝ) (g : Fin N → Fin 2 → Fin (k*k) → ℝ)
    (R : ℝ) :
    let q := krylovDegree k U (1/2) ε hk hU (by norm_num) (by norm_num) hε hε1
    (∀ Y : Matrix (Fin k) (Fin ((q+1)*b)) ℝ, ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ R) →
    ((automaticKrylovQueryProgram kernels T hT (fun w => P.columnBlocks hb w)
      S source j U ε hk hU hε hε1 N G g).work:ℝ) ≤
      4*q+15+(N:ℝ)*(source.cost+(3*q+2:ℕ)*P.cost+R+3*kernelEnvelope kernels k+212*(C+1)*(k:ℝ)^p) := by
  intro q hR
  have hh := columnBlocks_repeatedKrylovQueryProgram_work_bound kernels C p hC hp hK
    T hT P hb q S source j ε N G g R hR
  rw [automaticKrylovQueryProgram_work,Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_ofNat]
  change 4*(q:ℝ)+15+_ ≤ 4*(q:ℝ)+15+_
  exact add_le_add (le_refl _) hh

end
end HierarchicalAbsoluteSpectral
