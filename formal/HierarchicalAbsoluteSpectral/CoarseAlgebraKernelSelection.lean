import HierarchicalAbsoluteSpectral.CoarseAlgebraDenseOutputKernels

/-! Static circuit selection combines independently proved cost envelopes.
The selected object remains an ordinary arithmetic circuit; selection
inspects only dimensions and natural gate counts. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

def ArithmeticKernel.cheaper {n m p : ℕ} (K L : ArithmeticKernel n m p) :
    ArithmeticKernel n m p := if K.cost ≤ L.cost then K else L

@[simp] theorem ArithmeticKernel.cheaper_cost {n m p : ℕ}
    (K L : ArithmeticKernel n m p) : (K.cheaper L).cost = min K.cost L.cost := by
  unfold ArithmeticKernel.cheaper
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem ArithmeticKernel.cheaper_cost_le_left {n m p : ℕ}
    (K L : ArithmeticKernel n m p) : (K.cheaper L).cost ≤ K.cost := by simp

theorem ArithmeticKernel.cheaper_cost_le_right {n m p : ℕ}
    (K L : ArithmeticKernel n m p) : (K.cheaper L).cost ≤ L.cost := by simp

structure MatrixKernelCap where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  kernel : ArithmeticKernel rows inner columns

def MatrixKernelCap.Fits (cap : MatrixKernelCap) (a b c : ℕ) : Prop :=
  a ≤ cap.rows ∧ b ≤ cap.inner ∧ c ≤ cap.columns

def MatrixKernelCap.candidate (cap : MatrixKernelCap)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) : ArithmeticKernel a b c := by
  classical
  exact if h : cap.Fits a b c then cap.kernel.padShape
    (Fin.castLEEmb h.1) (Fin.castLEEmb h.2.1) (Fin.castLEEmb h.2.2)
  else fallback a b c

theorem MatrixKernelCap.candidate_cost (cap : MatrixKernelCap)
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) (h : cap.Fits a b c) :
    (cap.candidate fallback a b c).cost = cap.kernel.cost := by
  simp [MatrixKernelCap.candidate,h]

def offerKernelCap (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (cap : MatrixKernelCap) :
    ∀ a b c : ℕ, ArithmeticKernel a b c :=
  fun a b c => (fallback a b c).cheaper (cap.candidate fallback a b c)

theorem offerKernelCap_cost_le_fallback
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (cap : MatrixKernelCap) (a b c : ℕ) :
    (offerKernelCap fallback cap a b c).cost ≤ (fallback a b c).cost :=
  ArithmeticKernel.cheaper_cost_le_left _ _

theorem offerKernelCap_cost_le_cap
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (cap : MatrixKernelCap)
    (a b c : ℕ) (h : cap.Fits a b c) :
    (offerKernelCap fallback cap a b c).cost ≤ cap.kernel.cost := by
  exact (ArithmeticKernel.cheaper_cost_le_right _ _).trans_eq (cap.candidate_cost fallback a b c h)

def combineKernelCaps (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    List MatrixKernelCap → ∀ a b c : ℕ, ArithmeticKernel a b c
  | [] => fallback
  | cap::caps => offerKernelCap (combineKernelCaps fallback caps) cap

theorem combineKernelCaps_cost_le_fallback
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (caps : List MatrixKernelCap) (a b c : ℕ) :
    (combineKernelCaps fallback caps a b c).cost ≤ (fallback a b c).cost := by
  induction caps with
  | nil => exact le_rfl
  | cons cap caps ih => exact (offerKernelCap_cost_le_fallback _ cap a b c).trans ih

theorem combineKernelCaps_cost_le_cap
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c) (caps : List MatrixKernelCap)
    (cap : MatrixKernelCap) (hmem : cap ∈ caps) (a b c : ℕ) (h : cap.Fits a b c) :
    (combineKernelCaps fallback caps a b c).cost ≤ cap.kernel.cost := by
  induction caps with
  | nil => simp at hmem
  | cons head caps ih =>
    rcases List.mem_cons.mp hmem with heq | hrest
    · subst head
      exact offerKernelCap_cost_le_cap _ cap a b c h
    · exact (offerKernelCap_cost_le_fallback _ head a b c).trans (ih hrest)

end
end HierarchicalAbsoluteSpectral
