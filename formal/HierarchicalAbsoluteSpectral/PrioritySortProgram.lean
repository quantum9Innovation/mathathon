import HierarchicalAbsoluteSpectral.ArithmeticProgram
import Mathlib.Data.List.Sort

/-!
Counted comparison merge sort for Gaussian-priority row sampling. Every
comparison of real priorities is an arithmetic-program instruction. List
splitting, indexing and copying perform no real arithmetic.
-/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def priorityMergeProgram {ι : Type} (v : ι → ℝ) :
    List ι → List ι → ArithmeticProgram (List ι)
  | [], ys => .pure ys
  | xs, [] => .pure xs
  | x::xs, y::ys => .compare (v x) (v y) (fun b =>
      if b then do
        let zs ← priorityMergeProgram v xs (y::ys)
        ArithmeticProgram.pure (x::zs)
      else do
        let zs ← priorityMergeProgram v (x::xs) ys
        ArithmeticProgram.pure (y::zs))
termination_by xs ys => xs.length+ys.length

theorem priorityMergeProgram_eval {ι : Type} (v : ι → ℝ) (xs ys : List ι) :
    (priorityMergeProgram v xs ys).eval = xs.merge ys (fun i j => decide (v i≤v j)) := by
  match xs,ys with
  | [],ys => simp [priorityMergeProgram]
  | x::xs,[] => simp [priorityMergeProgram]
  | x::xs,y::ys =>
      by_cases h : v x≤v y <;>
        simp [priorityMergeProgram, ArithmeticProgram.eval, h,
          priorityMergeProgram_eval v xs (y::ys), priorityMergeProgram_eval v (x::xs) ys]
termination_by xs.length+ys.length

theorem priorityMergeProgram_work {ι : Type} (v : ι → ℝ) (xs ys : List ι) :
    (priorityMergeProgram v xs ys).work ≤ xs.length+ys.length := by
  match xs,ys with
  | [],ys => simp [priorityMergeProgram]
  | x::xs,[] => simp [priorityMergeProgram]
  | x::xs,y::ys =>
      have h₁ : (priorityMergeProgram v xs (y::ys)).work≤xs.length+ys.length+1 := by
        simpa [Nat.add_assoc] using priorityMergeProgram_work v xs (y::ys)
      have h₂ : (priorityMergeProgram v (x::xs) ys).work≤xs.length+ys.length+1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          priorityMergeProgram_work v (x::xs) ys
      by_cases h : v x≤v y <;>
        simp [priorityMergeProgram, ArithmeticProgram.work, h] <;> omega
termination_by xs.length+ys.length

theorem priorityMergeProgram_admissible {ι : Type} (v : ι → ℝ) (xs ys : List ι) :
    (priorityMergeProgram v xs ys).admissible := by
  match xs,ys with
  | [],ys => simp [priorityMergeProgram]
  | x::xs,[] => simp [priorityMergeProgram]
  | x::xs,y::ys =>
      by_cases h : v x≤v y <;>
        simp [priorityMergeProgram, ArithmeticProgram.admissible, h,
          priorityMergeProgram_admissible v xs (y::ys), priorityMergeProgram_admissible v (x::xs) ys]
termination_by xs.length+ys.length

def prioritySortProgram {ι : Type} (v : ι → ℝ) : List ι → ArithmeticProgram (List ι)
  | [] => .pure []
  | [x] => .pure [x]
  | x::y::xs => do
      let left := (x::y::xs).take (((x::y::xs).length+1)/2)
      let right := (x::y::xs).drop (((x::y::xs).length+1)/2)
      let a ← prioritySortProgram v left
      let b ← prioritySortProgram v right
      priorityMergeProgram v a b
termination_by xs => xs.length
decreasing_by all_goals simp; omega

theorem prioritySortProgram_eval {ι : Type} (v : ι → ℝ) : (xs : List ι) →
    (prioritySortProgram v xs).eval = xs.mergeSort (fun i j => decide (v i≤v j))
  | [] => by simp [prioritySortProgram]
  | [x] => by simp [prioritySortProgram]
  | x::y::xs => by
      rw [prioritySortProgram, List.mergeSort]
      have hl := prioritySortProgram_eval v
        ((x::y::xs).take (((x::y::xs).length+1)/2))
      have hr := prioritySortProgram_eval v
        ((x::y::xs).drop (((x::y::xs).length+1)/2))
      simp only [eval_bind, hl, hr, priorityMergeProgram_eval]
      simp [List.MergeSort.Internal.splitInTwo, List.splitAt_eq]
termination_by xs => xs.length
decreasing_by all_goals simp; omega

theorem prioritySortProgram_admissible {ι : Type} (v : ι → ℝ) : (xs : List ι) →
    (prioritySortProgram v xs).admissible
  | [] => by simp [prioritySortProgram]
  | [x] => by simp [prioritySortProgram]
  | x::y::xs => by
      rw [prioritySortProgram]
      have hl := prioritySortProgram_admissible v
        ((x::y::xs).take (((x::y::xs).length+1)/2))
      have hr := prioritySortProgram_admissible v
        ((x::y::xs).drop (((x::y::xs).length+1)/2))
      simp only [admissible_bind]
      exact ⟨hl,hr,priorityMergeProgram_admissible _ _ _⟩
termination_by xs => xs.length
decreasing_by all_goals simp; omega

theorem prioritySortProgram_work {ι : Type} (v : ι → ℝ) (k : ℕ) :
    ∀ xs : List ι, xs.length≤2^k → (prioritySortProgram v xs).work≤k*xs.length := by
  induction k with
  | zero =>
      intro xs h
      match xs with
      | [] => simp [prioritySortProgram]
      | [x] => simp [prioritySortProgram]
      | x::y::xs => simp at h
  | succ k ih =>
      intro xs h
      match xs with
      | [] => simp [prioritySortProgram]
      | [x] => simp [prioritySortProgram]
      | x::y::xs =>
          let l := (x::y::xs).take (((x::y::xs).length+1)/2)
          let r := (x::y::xs).drop (((x::y::xs).length+1)/2)
          have hl : l.length≤2^k := by simp [l, pow_succ] at h ⊢; omega
          have hr : r.length≤2^k := by simp [r, pow_succ] at h ⊢; omega
          have hs : l.length+r.length=(x::y::xs).length := by simp [l,r]; omega
          have hm := priorityMergeProgram_work v (prioritySortProgram v l).eval
            (prioritySortProgram v r).eval
          rw [prioritySortProgram_eval, prioritySortProgram_eval,
            List.length_mergeSort, List.length_mergeSort] at hm
          have h₁ := ih l hl
          have h₂ := ih r hr
          rw [prioritySortProgram]
          simp only [work_bind]
          change (prioritySortProgram v l).work+((prioritySortProgram v r).work+
            (priorityMergeProgram v (prioritySortProgram v l).eval
              (prioritySortProgram v r).eval).work) ≤ _
          rw [prioritySortProgram_eval, prioritySortProgram_eval]
          nlinarith

def priorityRows (n M : ℕ) (g : Fin n → ℝ) : Finset (Fin n) :=
  (((List.finRange n).mergeSort (fun i j => decide (g i≤g j))).take M).toFinset

theorem priorityRows_card (n M : ℕ) (hM : M≤n) (g : Fin n → ℝ) :
    (priorityRows n M g).card=M := by
  have hn : ((List.finRange n).mergeSort (fun i j => decide (g i≤g j))).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_finRange n)
  rw [priorityRows, List.toFinset_card_of_nodup hn.take, List.length_take,
    List.length_mergeSort, List.length_finRange, min_eq_left hM]

def priorityRowsProgram (n M : ℕ) (g : Fin n → ℝ) : ArithmeticProgram (Finset (Fin n)) := do
  let xs ← prioritySortProgram g (List.finRange n)
  ArithmeticProgram.pure ((xs.take M).toFinset)

@[simp] theorem priorityRowsProgram_eval (n M : ℕ) (g : Fin n → ℝ) :
    (priorityRowsProgram n M g).eval=priorityRows n M g := by
  simp only [priorityRowsProgram, eval_bind, eval_pure, prioritySortProgram_eval, priorityRows]

theorem priorityRowsProgram_admissible (n M : ℕ) (g : Fin n → ℝ) :
    (priorityRowsProgram n M g).admissible := by
  simp [priorityRowsProgram, prioritySortProgram_admissible]

theorem priorityRowsProgram_work (k M : ℕ) (g : Fin (2^k) → ℝ) :
    (priorityRowsProgram (2^k) M g).work≤k*2^k := by
  simp only [priorityRowsProgram, work_bind, work_pure, add_zero]
  simpa only [List.length_finRange] using
    prioritySortProgram_work g k (List.finRange (2^k)) (by simp)

end
end HierarchicalAbsoluteSpectral
