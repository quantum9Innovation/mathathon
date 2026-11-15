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
  | [],ys => rfl
  | x::xs,[] => rfl
  | x::xs,y::ys =>
      by_cases h : v x≤v y <;>
        simp [priorityMergeProgram, ArithmeticProgram.eval, List.merge, h,
          priorityMergeProgram_eval v xs (y::ys), priorityMergeProgram_eval v (x::xs) ys]
termination_by xs.length+ys.length

theorem priorityMergeProgram_work {ι : Type} (v : ι → ℝ) (xs ys : List ι) :
    (priorityMergeProgram v xs ys).work ≤ xs.length+ys.length := by
  match xs,ys with
  | [],ys => simp [priorityMergeProgram]
  | x::xs,[] => simp [priorityMergeProgram]
  | x::xs,y::ys =>
      have h₁ := priorityMergeProgram_work v xs (y::ys)
      have h₂ := priorityMergeProgram_work v (x::xs) ys
      by_cases h : v x≤v y <;>
        simp [priorityMergeProgram, ArithmeticProgram.work, h] <;> omega
termination_by xs.length+ys.length

theorem priorityMergeProgram_admissible {ι : Type} (v : ι → ℝ) (xs ys : List ι) :
    (priorityMergeProgram v xs ys).admissible := by
  match xs,ys with
  | [],ys => trivial
  | x::xs,[] => trivial
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

theorem prioritySortProgram_eval {ι : Type} (v : ι → ℝ) (xs : List ι) :
    (prioritySortProgram v xs).eval = xs.mergeSort (fun i j => decide (v i≤v j)) := by
  match xs with
  | [] => rfl
  | [x] => rfl
  | x::y::xs =>
      rw [prioritySortProgram, List.mergeSort]
      simp only [eval_bind, priorityMergeProgram_eval, prioritySortProgram_eval]
      rfl
termination_by xs.length
decreasing_by all_goals simp; omega

theorem prioritySortProgram_admissible {ι : Type} (v : ι → ℝ) (xs : List ι) :
    (prioritySortProgram v xs).admissible := by
  match xs with
  | [] => trivial
  | [x] => trivial
  | x::y::xs =>
      rw [prioritySortProgram]
      simp only [admissible_bind, prioritySortProgram_admissible,
        priorityMergeProgram_admissible, and_self]
termination_by xs.length
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
          change (prioritySortProgram v l).work+(prioritySortProgram v r).work+
            (priorityMergeProgram v (prioritySortProgram v l).eval
              (prioritySortProgram v r).eval).work ≤ _
          nlinarith

def priorityRows (n M : ℕ) (g : Fin n → ℝ) : Finset (Fin n) :=
  (((List.finRange n).mergeSort (fun i j => decide (g i≤g j))).take M).toFinset

end
end HierarchicalAbsoluteSpectral
