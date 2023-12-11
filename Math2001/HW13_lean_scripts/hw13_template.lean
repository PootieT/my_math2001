import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points MoP 9.1.10 Ex 7 -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp
  dsimp [(· ∣ ·)]
  push_neg
  use 5
  constructor
  . use 1; numbers
  . intro c
    obtain h0 | h1 := le_or_gt c 0
    · apply ne_of_gt
      calc
        20 * c ≤ 20 * 0 := by rel[h0]
        _ < 5 := by numbers
    · apply ne_of_lt
      have h1' : c ≥ 1 := by extra
      calc
        5 < 20 * 1 := by numbers
        _ ≤  20 * c := by rel[h1']

/- 3 points MoP 9.1.10 Ex 13 -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  dsimp
  intro x
  constructor
  . intro hx
    obtain ⟨c, hc⟩ := hx
    use -3*c + 4*x
    calc
      x = -27*x + 28*x := by ring
      _ = -3 * (9*x) + 7*(4*x) := by ring
      _ = -3 * (7*c) + 7*(4*x) := by rw[hc]
      _ = 7 * (-3*c+4*x) := by ring
  . intro hx
    obtain ⟨c, hc⟩ := hx
    use 9*c
    rw[hc]
    linarith

/- 4 points MoP 9.1.10 Ex 15 -/
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  dsimp
  intro x
  constructor
  . intro hx
    have h1 : (x+1)*(x+2)=0 := calc
      (x+1)*(x+2) = x^2 + 3*x + 2 := by ring
      _ =  0 := by rw[hx]
    rw [mul_eq_zero] at h1
    obtain h|h := h1
    . left
      linarith
    . right
      linarith
  . intro hx
    obtain hl|hr := hx
    . rw[hl]
      ring
    . rw[hr]
      ring

/- 3 points MoP 9.2.8 Ex 5 -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp
  intro x hx
  obtain ⟨c,hc⟩:= hx
  constructor
  . use 5*c+3
    calc
      x-1 = 6+ (x-7) := by ring
      _ = 6 + 10*c := by rw[hc]
      _ = 2 *(5*c+3) := by ring
  . use 1+2*c
    calc
      x-2 = 5 + (x-7) := by ring
      _ = 5 + 10*c := by rw[hc]
      _ = 5 * (1 + 2*c) := by ring

/- 3 points MoP 9.2.8 Ex 6 -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp
  intro x hx
  obtain ⟨c1,hc1⟩ := hx.left
  obtain ⟨c2,hc2⟩ := hx.right
  use 5*c2-3*c1
  calc
    x = 25*(x)-24*x := by ring
    _ = 25*(8*c2) - 24*x := by rw[hc2]
    _ = 25*(8*c2) - 24*(5*c1) := by rw[hc1]
    _ = 40*(5*c2 -3*c1) := by ring


/- 4 points MoP 9.2.8 Ex 7 -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp
  intro x hx
  obtain h|h:=hx
  . obtain ⟨a, ha⟩ := h
    dsimp[(.∣.)]
    push_neg
    obtain h_even | h_odd := Int.even_or_odd a
    . obtain ⟨b,hb⟩ := h_even
      have hx2 := calc
        x^2 = x*x := by ring
        _ = (3*a) * (3*a) := by rw[ha]
        _ = 9 * a* a := by ring
        _ = 9*(2*b)*a := by rw[hb]
        _ = 6*(3*a*b) := by ring
      have hx_mod : x^2  ≡ 0 [ZMOD 6] := by
        use 3*a*b
        linarith
      intro h_neg
      have H := calc
        0 ≡ x^2 [ZMOD 6] := by rel [hx_mod]
        _ ≡ 1 [ZMOD 6] := by rel [h_neg]
      numbers at H
    . obtain ⟨b,hb⟩ := h_odd
      have hx2 := calc
        x^2 = x*x := by ring
        _ = (3*a) * (3*a) := by rw[ha]
        _ = 9 * a* a := by ring
        _ = 9 * (2*b+1) * (2*b+1) := by rw [hb]
        _ = 6*(6*b^2 + 6*b + 1) + 3 := by ring
      have hx_mod : x^2  ≡ 3 [ZMOD 6] := by
        use 6*b^2 + 6*b + 1
        linarith
      intro h_neg
      have H := calc
        3 ≡ x^2 [ZMOD 6] := by rel [hx_mod]
        _ ≡ 1 [ZMOD 6] := by rel [h_neg]
      numbers at H
  . obtain ⟨a, ha⟩ := h
    dsimp[(.∣.)]
    push_neg
    mod_cases h_mod : a% 3
    . obtain ⟨b,hb⟩ := h_mod
      simp at hb
      have hx2 := calc
        x^2 = x*x := by ring
        _ = (2*a) * (2*a) := by rw[ha]
        _ = (2*(3*b)) * (2*a) := by rw [hb]
        _ = 6*(2*a*b) := by ring
      have hx_mod : x^2  ≡ 0 [ZMOD 6] := by
        use 2*a*b
        linarith
      intro h_neg
      have H := calc
        0 ≡ x^2 [ZMOD 6] := by rel [hx_mod]
        _ ≡ 1 [ZMOD 6] := by rel [h_neg]
      numbers at H
    . obtain ⟨b,hb⟩ := h_mod
      have hb: a = 3*b+1 := by addarith [hb]
      have hx2 := calc
        x^2 = x*x := by ring
        _ = (2*a) * (2*a) := by rw[ha]
        _ = (2*(3*b+1)) * (2*(3*b+1)) := by rw [hb]
        _ = 6*(6*b^2 + 4*b) + 4 := by ring
      have hx_mod : x^2  ≡ 4 [ZMOD 6] := by
        use (6*b^2 + 4*b)
        linarith
      intro h_neg
      have H := calc
        4 ≡ x^2 [ZMOD 6] := by rel [hx_mod]
        _ ≡ 1 [ZMOD 6] := by rel [h_neg]
      numbers at H
    . obtain ⟨b,hb⟩ := h_mod
      have hb: a = 3*b+2 := by addarith [hb]
      have hx2 := calc
        x^2 = x*x := by ring
        _ = (2*a) * (2*a) := by rw[ha]
        _ = (2*(3*b+2)) * (2*(3*b+2)) := by rw [hb]
        _ = 6*(6*b^2 + 8*b + 2) + 4 := by ring
      have hx_mod : x^2  ≡ 4 [ZMOD 6] := by
        use (6*b^2 + 8*b+2)
        addarith [hx2]
      intro h_neg
      have H := calc
        4 ≡ x^2 [ZMOD 6] := by rel [hx_mod]
        _ ≡ 1 [ZMOD 6] := by rel [h_neg]
      numbers at H
