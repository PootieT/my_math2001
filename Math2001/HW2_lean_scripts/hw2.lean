-- CS 511 Formal Methods HW2
import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

-- 5c De Morgan's Law 3
theorem problem5c {p q : Prop} (h : ¬ p ∧ ¬ q) : ¬ (p ∨ q) := by
   obtain ⟨h_not_p, h_not_q⟩ := h
   intros h_pq
   cases h_pq with 
    | inl l => apply h_not_p l
    | inr r => apply h_not_q r
  
-- 5d De Morgan's Law 4
theorem problem5d {p q : Prop} (h : ¬ p ∨  ¬ q) : ¬ (p ∧ q) := by
  intros h_pq
  obtain ⟨h_p, h_q⟩ := h_pq
  cases h with 
   | inl l => apply l h_p
   | inr r => apply r h_q


-- 6a: 1.4.11.1
theorem problem6a {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = (x + 3) - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1] 
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers

-- 6b: 1.4.11.2
theorem problem6b {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + 2 * b)/2 + 0.5 * a := by ring
    _ ≥ 4/2 + 0.5 * 3 := by rel [h1, h2]
    _ ≥ 3 := by numbers

-- 6c: 1.4.11.3
theorem problem6c {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x^3 - 8*x^2 + 2*x
      = x*x^2 - 8*x^2 + 2*x := by ring
    _ ≥ 9*x^2 - 8*x^2 + 2*x := by rel [hx]
    _ = x^2 + 2*x := by ring
    _ ≥ 9^2 + 2*9 := by rel[hx]
    _ ≥ 3 := by numbers
