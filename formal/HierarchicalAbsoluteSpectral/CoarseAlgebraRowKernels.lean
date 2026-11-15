import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelSelection

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matmul.RectangularPrograms

def rowForwardKernelCandidate {κ : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (m : ℕ) (hm : 0 < m)
    (a b c : ℕ) : ArithmeticKernel a b c := by
  classical
  exact if h : b ≤ m ∧ c ≤ width κ m then
    (blockedForwardKernel outer (max a m) m (width κ m) hm le_rfl).padShape
      (Fin.castLEEmb (le_max_left _ _)) (Fin.castLEEmb h.1) (Fin.castLEEmb h.2)
  else fallback a b c

def rowAdjointKernelCandidate {κ : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (m : ℕ) (hm : 0 < m)
    (a b c : ℕ) : ArithmeticKernel a b c := by
  classical
  exact if h : a ≤ m ∧ c ≤ width κ m then
    (blockedAdjointKernel outer (max b m) m (width κ m) hm le_rfl).padShape
      (Fin.castLEEmb h.1) (Fin.castLEEmb (le_max_left _ _)) (Fin.castLEEmb h.2)
  else fallback a b c

def rowSensitiveKernelFamily {κ : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (m : ℕ) (hm : 0 < m) :
    ∀ a b c : ℕ, ArithmeticKernel a b c := fun a b c =>
  (fallback a b c).cheaper
    ((rowForwardKernelCandidate fallback outer m hm a b c).cheaper
      ((rowAdjointKernelCandidate fallback outer m hm a b c).cheaper
        ((rowForwardKernelCandidate fallback outer m hm c b a).transpose.cheaper
          (rowAdjointKernelCandidate fallback outer m hm c b a).transpose)))

theorem rowSensitiveKernelFamily_cost_le_fallback {κ : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (m : ℕ) (hm : 0 < m) (a b c : ℕ) :
    (rowSensitiveKernelFamily fallback outer m hm a b c).cost ≤ (fallback a b c).cost := by
  exact ArithmeticKernel.cheaper_cost_le_left _ _

theorem rowSensitiveKernelFamily_row_bounds {κ η C : ℝ}
    (fallback : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (outer : ∀ m : ℕ, ArithmeticKernel m m (width κ m))
    (hC : 0 ≤ C)
    (hOuter : ∀ (N m b : ℕ) (hm : 0 < m) (hNm : m ≤ N) (hb : b ≤ width κ m),
      ((blockedForwardKernel outer N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) ∧
      ((blockedAdjointKernel outer N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η))
    (m : ℕ) (hm : 0 < m) (a b c : ℕ) :
    (b ≤ m → c ≤ width κ m →
      ((rowSensitiveKernelFamily fallback outer m hm a b c).cost:ℝ) ≤ C*(a+m:ℕ)*(m:ℝ)^(1+η)) ∧
    (a ≤ m → c ≤ width κ m →
      ((rowSensitiveKernelFamily fallback outer m hm a b c).cost:ℝ) ≤ C*(b+m:ℕ)*(m:ℝ)^(1+η)) ∧
    (a ≤ width κ m → b ≤ m →
      ((rowSensitiveKernelFamily fallback outer m hm a b c).cost:ℝ) ≤ C*(c+m:ℕ)*(m:ℝ)^(1+η)) ∧
    (a ≤ width κ m → c ≤ m →
      ((rowSensitiveKernelFamily fallback outer m hm a b c).cost:ℝ) ≤ C*(b+m:ℕ)*(m:ℝ)^(1+η)) := by
  have hforward (a b c : ℕ) (hb : b ≤ m) (hc : c ≤ width κ m) :
      ((rowForwardKernelCandidate fallback outer m hm a b c).cost:ℝ) ≤
        C*(a+m:ℕ)*(m:ℝ)^(1+η) := by
    simp only [rowForwardKernelCandidate,dif_pos (And.intro hb hc),ArithmeticKernel.padShape_cost]
    apply ((hOuter (max a m) m (width κ m) hm (le_max_right _ _) le_rfl).1).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply mul_le_mul_of_nonneg_left _ hC
    exact_mod_cast (show max a m ≤ a+m by omega)
  have hadjoint (a b c : ℕ) (ha : a ≤ m) (hc : c ≤ width κ m) :
      ((rowAdjointKernelCandidate fallback outer m hm a b c).cost:ℝ) ≤
        C*(b+m:ℕ)*(m:ℝ)^(1+η) := by
    simp only [rowAdjointKernelCandidate,dif_pos (And.intro ha hc),ArithmeticKernel.padShape_cost]
    apply ((hOuter (max b m) m (width κ m) hm (le_max_right _ _) le_rfl).2).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply mul_le_mul_of_nonneg_left _ hC
    exact_mod_cast (show max b m ≤ b+m by omega)
  have hmin : (rowSensitiveKernelFamily fallback outer m hm a b c).cost =
      min (fallback a b c).cost (min (rowForwardKernelCandidate fallback outer m hm a b c).cost
        (min (rowAdjointKernelCandidate fallback outer m hm a b c).cost
          (min (rowForwardKernelCandidate fallback outer m hm c b a).cost
            (rowAdjointKernelCandidate fallback outer m hm c b a).cost))) := by
    simp [rowSensitiveKernelFamily]
  constructor
  · intro hb hc
    apply le_trans _ (hforward a b c hb hc)
    exact_mod_cast hmin ▸ (min_le_right _ _).trans (min_le_left _ _)
  constructor
  · intro ha hc
    apply le_trans _ (hadjoint a b c ha hc)
    exact_mod_cast hmin ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  constructor
  · intro ha hb
    apply le_trans _ (hforward c b a hb ha)
    exact_mod_cast hmin ▸ (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · intro ha hc
    apply le_trans _ (hadjoint c b a hc ha)
    exact_mod_cast hmin ▸ (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

end
end HierarchicalAbsoluteSpectral
