import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

/- 2 points MoP 8.1.13 Ex 15 -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x↦x -- use this identify function as the f function, and show 2*f is not surjective
  constructor
  . -- goal is to show identity function works
    intro h
    use h
    simp
  . -- goal is to show 2*f is not surjective
    use 3
    intro h
    simp
    obtain h0 | h1 := le_or_succ_le h 1
    . -- if h ≤ 0
      have h0': 2*h < 3 := by
        calc
          2*h ≤ 2*1 := by rel[h0]
          _ = 2 := by ring
          _ < 3 := by numbers
      linarith
    . -- if 1 ≤ h
      have h1': 2*h > 3 := by
        calc
          2*h ≥ 2*2 := by rel[h1]
          _ = 4 := by ring
          _ > 3 := by numbers
      linarith


/- 2 points MoP 8.1.13 Ex 16 -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp[Surjective]
  push_neg
  use 0  -- if c is 0
  simp
  use 1  -- then output cannot be mapped to 1
  numbers

/- 3 points MoP 8.1.13 Ex 17 -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp[Injective]
  push_neg
  intro x y h
  have h1 := lt_trichotomy x y
  obtain h_lt | h_eq | h_gt := h1
  . -- x < y
    have h_c := hf x y
    have h_neq := ne_of_lt (h_c h_lt)
    contradiction
  . -- x=y
    apply h_eq
  . -- x > y
    have h_c := hf y x
    have h_neq := ne_of_gt (h_c h_gt)
    contradiction

/- 3 points MoP 8.1.13 Ex 18 -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp[Surjective]
  intro x
  simple_induction x with k hk
  . use x0
    apply h0
  . obtain ⟨x, hk⟩ := hk
    use i x
    rw [hi, hk]

/- 2 points MoP 8.2.8 Ex 1 -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp[Bijective, Injective, Surjective]
  constructor
  . intro x y h
    have h1 : -3*x = -3*y := by
      calc
        -3*x = -4+ (4-3*x) := by ring
        _ = -4 + (4 - 3*y) := by rw[h]
        _ = -3*y := by ring
    cancel -3 at h1
  . intro x
    use (4-x)/3
    linarith

/- 2 points MoP 8.2.8 Ex 2 -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp[Bijective, Injective, Surjective]
  by_cases h: Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x)
  . -- assuming not bijective, then contradiction hopefully
    obtain ⟨hin, hsu⟩ := h
    dsimp[Bijective, Injective, Surjective] at hin hsu
    have h_not_in: ¬ ∀ ⦃a₁ a₂ : ℝ⦄, a₁ ^ 2 + 2 * a₁ = a₂ ^ 2 + 2 * a₂ → a₁ = a₂:=by
      push_neg
      use -3, 1
      constructor
      . ring
      . numbers
    contradiction
  . -- otherwise it is our hypothesis
    apply h

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

/- 3 points MoP 8.3.10 Ex 2 -/
theorem problem5c : Inverse u v := by
  dsimp[Inverse]
  constructor
  . ext x
    dsimp [v, u]
    linarith
  . ext x
    dsimp [v, u]
    linarith

/- 3 points MoP 8.3.10 Ex 3 -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp[Injective]
  intro x y h
  apply hf (hg h)
