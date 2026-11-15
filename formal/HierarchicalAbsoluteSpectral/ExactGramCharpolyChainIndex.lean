import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Hom.Basic

/-!
Enumerating downward-closed generator/exponent labels as variable-length
chains.  This file depends only on the finite labels, not on a Krylov state,
matrix, rank-profile program, or characteristic-polynomial algorithm.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

variable {n w : ℕ}

/-- The selected positions belonging to one generator. -/
abbrev ExactGramChainFiber (label : Fin w ↪o (Fin n ×ₗ ℕ)) (g : Fin n) :=
  {i : Fin w // (ofLex (label i)).1 = g}

/-- Every earlier exponent of a selected generator also occurs. -/
def ExactGramChainDownward (label : Fin w ↪o (Fin n ×ₗ ℕ)) : Prop :=
  ∀ (i : Fin w) (q : ℕ), q ≤ (ofLex (label i)).2 →
    ∃ k : Fin w, label k = toLex ((ofLex (label i)).1, q)

/-- The length of a chain is the number of selected positions in its fiber. -/
def exactGramChainLength (label : Fin w ↪o (Fin n ×ₗ ℕ)) (g : Fin n) : ℕ :=
  Fintype.card (ExactGramChainFiber label g)

theorem exactGramChainExponent_injective (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (g : Fin n) :
    Function.Injective (fun i : ExactGramChainFiber label g => (ofLex (label i.val)).2) := by
  intro i j hij
  apply Subtype.ext
  apply label.injective
  apply ofLex.injective
  exact Prod.ext (i.property.trans j.property.symm) hij

/-- Downward closure forces the exponent to be smaller than the fiber's
cardinality.  The first `exponent+1` labels inject into that same fiber. -/
theorem exactGramChainExponent_lt_length (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n)
    (i : ExactGramChainFiber label g) :
    (ofLex (label i.val)).2 < exactGramChainLength label g := by
  classical
  let e := (ofLex (label i.val)).2
  have hwitness : ∀ q : Fin (e+1),
      ∃ k : ExactGramChainFiber label g, (ofLex (label k.val)).2 = q.val := by
    intro q
    obtain ⟨k, hk⟩ := hdown i.val q.val (Nat.le_of_lt_succ q.isLt)
    refine ⟨⟨k, ?_⟩, ?_⟩
    · have hg := congrArg (fun x => (ofLex x).1) hk
      exact hg.trans i.property
    · exact congrArg (fun x => (ofLex x).2) hk
  let f : Fin (e+1) → ExactGramChainFiber label g :=
    fun q => Classical.choose (hwitness q)
  have hf : ∀ q : Fin (e+1), (ofLex (label (f q).val)).2 = q.val :=
    fun q => Classical.choose_spec (hwitness q)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    calc
      a.val = (ofLex (label (f a).val)).2 := (hf a).symm
      _ = (ofLex (label (f b).val)).2 :=
        congrArg (fun x : ExactGramChainFiber label g => (ofLex (label x.val)).2) hab
      _ = b.val := hf b
  have hcard := Fintype.card_le_of_injective f hinj
  exact Nat.lt_of_succ_le (by
    simpa only [Fintype.card_fin, exactGramChainLength, e, Nat.succ_eq_add_one] using hcard)

theorem exactGramChainLength_le_w (label : Fin w ↪o (Fin n ×ₗ ℕ)) (g : Fin n) :
    exactGramChainLength label g ≤ w := by
  simpa only [exactGramChainLength, Fintype.card_fin] using
    Fintype.card_subtype_le (fun i : Fin w => (ofLex (label i)).1 = g)

theorem exactGramChainLength_sum (label : Fin w ↪o (Fin n ×ₗ ℕ)) :
    ∑ g : Fin n, exactGramChainLength label g = w := by
  have h := Fintype.card_congr
    (Equiv.sigmaFiberEquiv (fun i : Fin w => (ofLex (label i)).1))
  simpa only [Fintype.card_sigma, Fintype.card_fin, exactGramChainLength] using h

/-- The exponent itself is the canonical finite index within its chain. -/
def exactGramChainIndexMap (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n) :
    ExactGramChainFiber label g → Fin (exactGramChainLength label g) :=
  fun i => ⟨(ofLex (label i.val)).2, exactGramChainExponent_lt_length label hdown g i⟩

theorem exactGramChainIndexMap_bijective (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n) :
    Function.Bijective (exactGramChainIndexMap label hdown g) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j hij
    apply exactGramChainExponent_injective label g
    exact congrArg Fin.val hij
  · exact (Fintype.card_fin (exactGramChainLength label g)).symm

/-- Each generator's positions are equivalent to the initial exponent
interval, with no arbitrary reordering of those exponents. -/
noncomputable def exactGramChainIndex (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n) :
    ExactGramChainFiber label g ≃ Fin (exactGramChainLength label g) :=
  Equiv.ofBijective (exactGramChainIndexMap label hdown g)
    (exactGramChainIndexMap_bijective label hdown g)

@[simp] theorem exactGramChainIndex_val (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n)
    (i : ExactGramChainFiber label g) :
    (exactGramChainIndex label hdown g i).val = (ofLex (label i.val)).2 := rfl

theorem exactGramChainIndex_inverse_label (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) (g : Fin n)
    (q : Fin (exactGramChainLength label g)) :
    label ((exactGramChainIndex label hdown g).symm q).val = toLex (g, q.val) := by
  apply ofLex.injective
  apply Prod.ext
  · exact ((exactGramChainIndex label hdown g).symm q).property
  · have h := exactGramChainIndex_val label hdown g
      ((exactGramChainIndex label hdown g).symm q)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- The complete indexing data needed to enumerate diagonal companion blocks. -/
structure ExactGramChainIndexData (label : Fin w ↪o (Fin n ×ₗ ℕ)) where
  length : Fin n → ℕ
  index : ∀ g, ExactGramChainFiber label g ≃ Fin (length g)
  index_val : ∀ g (i : ExactGramChainFiber label g),
    (index g i).val = (ofLex (label i.val)).2
  inverse_label : ∀ g (q : Fin (length g)),
    label ((index g).symm q).val = toLex (g, q.val)
  sum_length : ∑ g : Fin n, length g = w
  length_le_w : ∀ g, length g ≤ w

/-- Construct the lengths and exact exponent-index equivalences from the
generic downward-closure invariant. -/
noncomputable def exactGramChainIndexData (label : Fin w ↪o (Fin n ×ₗ ℕ))
    (hdown : ExactGramChainDownward label) : ExactGramChainIndexData label where
  length := exactGramChainLength label
  index := exactGramChainIndex label hdown
  index_val := exactGramChainIndex_val label hdown
  inverse_label := exactGramChainIndex_inverse_label label hdown
  sum_length := exactGramChainLength_sum label
  length_le_w := exactGramChainLength_le_w label

end HierarchicalAbsoluteSpectral
