import Mathlib.Data.Real.Basic
axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

-- 3a slide 21
theorem prob_3a {p q r : Prop} (h : p ∧ q → r) : p → (q → r) := by
intro h_p
intro h_q
have h_pq : p ∧ q  := by apply And.intro h_p h_q
apply h h_pq


-- 3b slide 23

theorem prob_3b {p q r : Prop} (h : p → (q → r)) : (p → q) → (p → r) := by
intro h_pq
intro h_p
have h_q : q := by apply h_pq h_p
have h_qr : q → r := by apply h h_p
apply h_qr h_q  -- always end on an apply

-- 3c slide 24

theorem prob_3c {p q r : Prop} (h : p ∧ ¬q → r) (h_nr: ¬r) (h_p: p) : q := by
have h_nnq : ¬¬q := by 
  intro h_nq
  have h_pnq: p ∧ ¬q := by apply And.intro h_p h_nq 
  have h_r: r := by apply h h_pnq
  contradiction
apply notnotE h_nnq
 

-- 4a (example 1.3.1)
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := 
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- 4b (example 1.3.2)
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc 
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- 4c (example 1.3.3)
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * (b + 2) - 10 := by ring
    _ = 4 + 5 * 3 - 10 := by rw [h2]
    _ = 9 := by ring

