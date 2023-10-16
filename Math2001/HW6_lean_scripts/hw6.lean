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

-- 4a) MoP Sec 5.1.7 Exercise 11
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h1
    obtain ⟨x, hx⟩ := h1  
    use x
    have hpqx: P x ↔ Q x := h x
    obtain ⟨hpq, hqp⟩ := hpqx  
    apply hpq hx
  . intro h2
    obtain ⟨x, hx⟩ := h2
    use x
    have hpqx: P x ↔ Q x := h x
    obtain ⟨hpq, hqp⟩ := hpqx  
    apply hqp hx

-- 4b) MoP Sec 5.1.7 Exercise 12
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h1
    obtain ⟨x, hx⟩ := h1 
    obtain ⟨y, hy⟩ := hx 
    use y
    use x
    apply hy
  . intro h1
    obtain ⟨x, hx⟩ := h1 
    obtain ⟨y, hy⟩ := hx 
    use y
    use x
    apply hy

-- 4c) MoP Sec 5.1.7 Exercise 13
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro h1
    intro y
    intro x
    apply h1
  . intro h1
    intro y
    intro x
    apply h1

-- 4d) MoP Sec 5.1.7 Exercise 14
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h1
    obtain ⟨hx, hq⟩ := h1 
    obtain ⟨x, hx'⟩ := hx 
    use x
    apply And.intro hx' hq
  . intro h1
    obtain ⟨x, hxq⟩ := h1 
    obtain ⟨hx, hq⟩ := hxq 
    constructor
    . use x
      apply hx
    . apply hq

-- 5a) MoP Sec 5.2.7 Exercise 1
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  -- strategy here is to show 0 works, 2 does not work, so doesn't matter if 1 works or not 
  -- (it actually works but just hard to prove), we have our theorem
  by_cases h0: Tribalanced 1
  . use 1
    dsimp[Tribalanced] at *
    constructor
    . apply h0
    . simp
      use 1
      numbers
  . use 0
    constructor
    . intro n
      conv => ring
      numbers
    . conv => ring
      apply h0

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

-- 5a) MoP Sec 5.2.7 Exercise 3
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one 
  . intro h2
    dsimp [Superpowered] at h2
    have h5_prime: Prime (2^2^5 + 1) := by apply h2 5
    have h5_not_prime: ¬ Prime (2^2^5 + 1) := by
      apply not_prime 641 6700417
      . numbers
      . numbers
      . numbers
    contradiction  


