import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- Problem 4a) MoP 5.3.5
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2^2 := by numbers
      _ ≤ (n)^2 := by rel [hn]

-- Problem 4b) MoP 5.3.6 Exercise 2
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro h
    by_cases hP : P
    . constructor
      . apply hP
      . intro hQ
        have h2 : P → Q := by
          intro hP1
          apply hQ
        contradiction
    . constructor
      . apply False.elim
        apply h
        intro hP1
        by_cases hQ: Q
        . apply hQ
        . contradiction
      . intro hQ
        have h2 : P → Q := by
          intro hP1
          apply hQ
        contradiction
  . intro h
    obtain ⟨ hP , h_not_Q⟩ := h
    intro hPtoQ
    have hQ :Q  :=  by apply hPtoQ hP
    contradiction


-- Problem 5a) MoP 5.3.6 Exercise 9
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h
  use k
  constructor
  . apply hk
  . constructor
    . apply hk1
    . apply hkp


-- Problem 5b) MoP 5.3.6 Exercise 10
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    apply hp
    apply prime_test
    . apply hp2
    . apply H
  push_neg at H
  apply H
