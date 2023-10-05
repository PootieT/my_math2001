import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 4a) MoP Sec 3.1 Example 3.1.4
def theorem4a {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1 
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring
  
-- 4b) MoP Sec 3.1 Example 3.1.6
def theorem4b {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] 
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2*a*b + 3*b + a + 1
  calc 
    x*y + 2*y = (2*a + 1)*(2*b + 1) + 2*(2*b+1) := by rw [ha, hb]
    _ = 2*(2*a*b + 3*b + a + 1) + 1 := by ring


-- 4c) MoP Sec 3.1 Example 3.1.8
def theorem4c {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2*k^2 + 2*k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k+k)^2 + 2*(k+k) - 5 := by rw [hk]
    _ = 4 * k^2 + 4*k - 5 := by ring
    _ = 2 * (2*k^2 + 2*k - 3) + 1 := by ring


-- 4d) MoP Sec 3.1 Exercise 3.1.10 exercise 14
def theorem4d (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha_even | ha_odd := Int.even_or_odd a
  . obtain ⟨x, hx⟩ := ha_even
    obtain hb_even | hb_odd := Int.even_or_odd b
    . left
      obtain ⟨y, hy⟩ := hb_even
      have hab: Even (a-b) := by
        use x-y
        calc
          a-b = 2 * x- 2*y := by rw[hx, hy]
          _ = (x-y) + (x-y) := by ring
      apply hab
    . obtain hc_even | hc_odd := Int.even_or_odd c
      . right
        left
        obtain ⟨z, hz⟩ := hc_even
        have hac: Even (a+c) := by
          use x+z
          calc
            a+c = 2 * x + 2*z := by rw[hx, hz]
            _ = (x+z) + (x+z) := by ring
        apply hac
      . right
        right
        obtain ⟨z, hz⟩ := hc_odd
        obtain ⟨y, hy⟩ := hb_odd
        have hbc: Even (b-c) := by
          use y-z
          calc
            b-c = 2 * y +1 - (2*z + 1) := by rw[hy, hz]
            _ = (y-z) + (y-z) := by ring
        apply hbc
  . obtain ⟨x, hx⟩ := ha_odd
    obtain hb_even | hb_odd := Int.even_or_odd b
    . obtain ⟨y, hy⟩ := hb_even
      obtain hc_even | hc_odd := Int.even_or_odd c
      . right
        right
        obtain ⟨z, hz⟩ := hc_even
        have hbc: Even (b-c) := by
          use y-z
          calc
            b-c = 2 * y- 2*z := by rw[hy, hz]
            _ = (y-z) + (y-z) := by ring
        apply hbc
      . right 
        left
        obtain ⟨z, hz⟩ := hc_odd
        have hac: Even (a+c) := by
          use x+z + 1
          calc
            a+c = 2 * x + 1 + (2*z + 1) := by rw[hx, hz]
            _ = (x+z+1) + (x+z+1) := by ring
        apply hac
    . left
      obtain ⟨y, hy⟩ := hb_odd
      have hab: Even (a-b) := by
        use x-y
        calc
          a-b = 2 * x+1- (2*y+1) := by rw[hx, hy]
          _ = (x-y) + (x-y) := by ring
      apply hab



-- 5a) MoP Sec 4.1 Example 4.1.3
def theorem5a {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hab: (a+b)/2 ≥ a ∨ (a+b)/2 ≤ b := by apply h
  obtain h1 | h1 := hab
  . calc
    b = 2* ((a+b)/2) - a := by ring
    _ ≥ 2*a - a := by rel [h1]
    _ = a := by ring
  . calc
    a = 2* ((a+b)/2) - b := by ring
    _ ≤  2*b - b := by rel [h1]
    _ = b := by ring

-- 5b) MoP Sec 4.1 Example 4.1.6
-- lemma abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=

def theorem5b : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intros x y
  intro h
  have hxy : -3 ≤ x+y ∧ x+y ≤ 3 
  . apply abs_le_of_sq_le_sq' 
    calc 
      (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra
      _ = 2*(x^2 + y^2) := by ring
      _ ≤ 2 * 4 := by rel [h]  
      _ ≤ 3 ^ 2 := by numbers 
    numbers
  obtain ⟨hl, hr⟩ := hxy
  apply hl 


-- 5c) MoP Sec 4.1 Exercise 2 4.1.10
def theorem5c {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h5 : 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5
  simp at h5
  have h3 : 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3
  simp at h3
  dsimp [(· ∣ ·)]
  obtain ⟨x, hx⟩ := h3
  obtain ⟨y, hy⟩ := h5
  use 2*x - 3*y
  calc
    n = 10*n - 9*n := by ring
    _ = 10* (3*x) - 9*n := by rw [hx]
    _ = 10* (3*x) - 9 * (5 * y) := by rw [hy]
    _ = 15 * (2 * x - 3 * y) := by ring


-- 5d) MoP Sec 4.1 Exercise 4 4.1.10
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
def theorem5d : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 10
  intro n hn
  calc
    n ^ 3 + 3 * n = n * (n^2 + 3) := by ring
    _ ≥ 10 * (n^2 + 3) := by rel[hn]
    _ = 10*n^2 + 30 := by ring
    _ = 7*n ^ 2 + 3 * n^2 + 30 := by ring
    _ ≥  7*n ^ 2 + 3*10^2 + 30 := by rel[hn]
    _ =  7*n ^2 + 12 + 318 := by ring
    _ ≥  7*n ^2 + 12 := by extra


-- 6a) MoP Sec 4.2 Example 4.2.5
def theorem6a {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h_rewrite : (x+3) * (x-2) = 0 :=  
    calc
      (x+3) * (x-2) = x ^ 2 + x - 6 := by ring
      _ = 0 := by rw [h]
    have H : (x+3 = 0) ∨ (x -2 = 0) := by apply eq_zero_or_eq_zero_of_mul_eq_zero h_rewrite
    obtain h3 | h2 := H
    left
    . calc 
      x = x+3 - 3 := by ring
      _ = 0 - 3 := by rw[h3]
      _ = -3 := by numbers
    right
    . calc 
      x = x-2 + 2 := by ring
      _ = 0 + 2 := by rw[h2]
      _ = 2 := by numbers
  . intro h
    obtain h1 | h2 := h
    . calc 
      x ^2 + x - 6 = (-3)^2 + (-3) - 6 := by rw[h1]
      _ = 0 := by numbers
    . calc 
      x ^2 + x - 6 = (2)^2 + (2) - 6 := by rw[h2]
      _ = 0 := by numbers

-- 6b) MoP Sec 4.2 Example 4.2.6
def theorem6b {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h0: 0 ≤ 1 := by numbers
    have ha: -1≤(2*a-5)∧ (2*a-5)≤1
    . apply abs_le_of_sq_le_sq'
      calc
        (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) +5 := by ring
        _ ≤ 4*(-1) +5 := by rel [h]
        _ = 1^2 := by numbers
      numbers
    obtain ⟨ h1, h2 ⟩ := ha
    have h3: 2*a ≥ 2*2 := by
      calc
        2*a = (2*a-5) + 5:= by ring
        _ ≥ (-1) + 5 := by rel [h1]
        _ = 2*2 := by extra
    cancel 2 at h3
    have h5: 2*a ≤ 2*3 := by
      calc
        2*a = (2*a-5) + 5:= by ring
        _ ≤  (1) + 5 := by rel [h2]
        _ = 2*3 := by extra
    cancel 2 at h5
    interval_cases a
    . left
      numbers
    . right
      numbers
  . intro h
    obtain h1 | h2 := h
    . calc 
      a ^ 2 - 5 * a + 5 = (2)^2 - 5*2 + 5 := by rw [h1]
      _ ≤ -1 := by numbers
    . calc
      a ^ 2 - 5 * a + 5 = (3)^2 - 5*3 + 5 := by rw [h2]
      _ ≤ -1 := by numbers