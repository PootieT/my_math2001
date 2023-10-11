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

-- 4a) MoP Sec 4.2.10 Exercise 2
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  dsimp [(· ∣ ·)] at *
  constructor
  . intro hn
    obtain ⟨a, ha⟩ := hn
    constructor
    . use 9*a
      calc
        n = 63*a := by rw[ha]
        _ = 7* (9*a) := by ring
    . use 7*a
      calc
        n = 63*a := by rw[ha]
        _ = 9* (7*a) := by ring
  . intro hn 
    obtain ⟨h1, h2⟩ := hn
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    use 4*b - 3*a
    calc
      n = 28*n - 27*n := by ring
      _ = 28*(9*b) - 27*n := by rw[hb]
      _ = 28*(9*b) - 27*(7*a) := by rw[ha]
      _ = 63 * (4*b - 3*a) := by ring
    

-- 4b) MoP Sec 4.2.10 Exercise 5
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have h1:= by calc
      k*k = k^2 := by ring
      _ ≤ 6 := by rel [h] 
      _ < 9 := by numbers
      _ = 3*3 := by ring
    rw [← Nat.mul_self_lt_mul_self_iff] at h1
    interval_cases k
    . ring
    . right
      left
      ring
    . right 
      right
      ring
  . intro h
    obtain h1| h2| h3 := h
    extra
    rw[h2]
    numbers
    rw[h3]
    numbers

-- 5a) MoP Sec 4.3.2 
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intro a
    intro h1
    intro h3
    have h1': a - 2 ≥ -1 := by 
      calc
        a - 2 ≥ 1 - 2 := by rel[h1]
        _ = -1 := by ring
    have h3' := by
      calc 
        a - 2 ≤ 3 - 2 := by rel[h3]
        _ = 1 := by numbers 
    have h_sq := by apply sq_le_sq' h1' h3'
    calc
      (a - 2)^2 ≤ 1 ^ 2 := by rel[h_sq]
      _ = 1 := by numbers 
  . intro y hy
    have h1 := hy 1 (by numbers) (by numbers)
    have h3 := hy 3 (by numbers) (by numbers)
    have h_neg := by
      calc 
        (y-2)^2 = ((1-y)^2 + (3-y)^2 - 2)/2 := by ring
        _ ≤ (1+(3-y)^2-2)/2 := by rel[h1]
        _ ≤ (1+1-2)/2 := by rel[h3]
        _ = 0 := by numbers
    have h_pos : (y-2)^2 ≥ 0 := by extra 
    have h2: (y-2)^2 =0 := by apply le_antisymm' h_neg h_pos
    cancel 2 at h2
    addarith[h2]

-- 5b) MoP Sec 4.3.5 Exercise 1
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . numbers
  . intro y hy
    calc
      y = ((4*y-3) +3)/4 := by ring
      _ = (9 + 3)/4 := by rw [hy]
      _ = 3 := by numbers

-- 5c) MoP Sec 4.3.5 Exercise 2
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . extra
  . intro y hy
    obtain h1 | h2 := Nat.eq_zero_or_pos y
    . extra
    . specialize hy 0
      simp at hy
      apply hy
      
-- 6a) Mop Sec 4.4.4
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  . right
    have hmp2: m≤p := by apply Nat.le_of_dvd hp' hmp
    obtain h1 | h2 : m = p ∨ m < p := eq_or_lt_of_le hmp2
    apply h1
    have h_contra := by apply H m hm_left h2 hmp
    contradiction

-- 6b) Mop Sec 4.4.5
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain ha_l | ha_g := lt_or_ge a 3 
  . have ha_l': a ≤ 2 := by addarith[ha_l] 
    obtain hb_l | hb_g := lt_or_ge b 2
    . have hb_l': b≤1 := by addarith[hb_l]
      have hc2 := by
        calc
          c^2 = a^2 + b^2 := by rw[h_pyth]
          _ ≤ 2^2 + b^2 := by rel[ha_l'] 
          _ ≤ 2^2 + 1^2 := by rel[hb_l'] 
          _ < 3^2 := by numbers
      cancel 2 at hc2
      interval_cases c
      . interval_cases a
        . interval_cases b
          . contradiction
        . interval_cases b
          . contradiction
      . interval_cases a
        . interval_cases b
          . contradiction
        . interval_cases b
          . contradiction
    . have hb2 := by 
        calc
          b^2 < a^2 + b^2 := by extra
          _ = c^2 := by rw[h_pyth]
      cancel 2 at hb2
      have hb3: b+1 ≤c := by addarith[hb2]
      have hc3 := by
        calc
          c^2 = a^2 + b^2 := by rw[h_pyth]
          _ = a*a + b^2 := by ring
          _ ≤ 2*2 + b^2 := by rel[ha_l']
          _ = b^2 + 2*2 := by ring
          _ ≤ b^2 + 2*b := by rel[hb_g]
          _ < b^2 + 2*b + 1 := by extra
          _ = (b+1)^2 := by ring
      cancel 2 at hc3
      have hbc := calc
        b+1 ≤ c := by rel[hb3]
        _ < b+1 := by rel[hc3]
      have h_contra: 1<1 := by addarith[hbc]
      contradiction
  . apply ha_g 
    

-- 6c) Mop Sec 4.4.6 Exercise 1
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

-- 6d) Mop Sec 4.4.6 Exercise 5
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, H⟩ := h
  obtain h_gt | h_eq := lt_or_eq_of_le hp
  . right
    have h_odd: ¬Nat.Even p:= by
      intro h_even
      obtain ⟨x, hx⟩ := h_even
      have h_div_2: 2 ∣ p := by
        use x
        rw [hx]
      obtain h2 := H 2 h_div_2
      obtain hl| hr := h2
      . contradiction
      . rw [hr] at h_gt
        have h_gt': 0<0 := by addarith[h_gt]
        contradiction
  . left
    rw[h_eq]