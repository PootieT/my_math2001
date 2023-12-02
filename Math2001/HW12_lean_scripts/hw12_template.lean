import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
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
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points MoP 8.3.10 Ex 4 -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp[Surjective] at hf
  dsimp[Surjective] at hg
  dsimp[Surjective]
  intro z
  have hy := (hg z)
  obtain ⟨a,ha⟩ := hy
  have hx := (hf a)
  obtain ⟨b,hb⟩ := hx
  use b
  rw[hb]
  rw[ha]


/- 2 points MoP 8.3.10 Ex 5 -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp[Surjective]
  choose g hg using hf
  use g
  ext b
  apply hg


/- 2 points MoP 8.3.10 Ex 6 -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp[Inverse]
  obtain ⟨hgf, hfg⟩ := h
  constructor
  . apply hfg
  . apply hgf


theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl

/- 3 points MoP 8.3.10 Ex 7 -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp[Inverse]
  ext y
  have hg1 := (g1 y)
  have hg2 := (g2 y)
  have h_biject := bijective_of_inverse h1
  dsimp[Bijective, Injective, Surjective] at h_biject
  obtain ⟨h_inject,h_surject⟩ := h_biject
  obtain ⟨x, hfx⟩ := h_surject y
  have hfx': y = f x := by rw[hfx]
  rw [hfx']
  dsimp[Inverse] at h1
  obtain ⟨hg1f, hfg1⟩ := h1
  obtain ⟨hg2f, hfg2⟩ := h2
  calc
    g1 (f x) = (g1 ∘ f) x := by rfl
    _ = id x := by rw[hg1f]
    _ = (g2 ∘ f) x := by rw[hg2f]
    _ = g2 (f x) := by rfl

/- 1 points MoP 8.4.10 Ex 2 -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Injective]
  push_neg
  use (0,0), (2, 1)
  ring

/- 1 points MoP 8.4.10 Ex 2 -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Surjective]
  intro x
  use (x + 1, 0)
  ring

/- 2 points MoP 8.4.10 Ex 3 -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp[Surjective]
  push_neg
  use -1
  intro t
  apply ne_of_gt
  have h_neg : t.fst ^ 2 + t.snd ^ 2 > -1 := by
    calc
      t.fst ^ 2 + t.snd ^ 2 ≥  t.fst ^ 2 + 0 := by extra
      _ ≥ 0 + 0 := by extra
      _ > -1 := by ring
  apply h_neg

/- 3 points MoP 8.4.10 Ex 6 -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp[Injective]
  push_neg
  use (0,0,0), (1, -2, 1)
  ring
  constructor
  . ring
  . numbers

/- 3 points MoP 8.4.10 Ex 7 -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp[Injective]
  intro t1 t2 h
  obtain ⟨h1, h2, h3⟩ := h
  calc
    t1 = (t1.fst, t1.snd) := by ring
    _ = (2*(t1.fst + t1.snd)-(t1.fst + 2*t1.snd), (t1.fst+2 * t1.snd)-(t1.fst + t1.snd)) := by ring
    _ = (2*(t2.fst + t2.snd)-(t2.fst + 2*t2.snd), (t1.fst+2 * t1.snd)-(t1.fst + t1.snd)) := by rw[h1, h2]
    _ = (2*(t2.fst + t2.snd)-(t2.fst + 2*t2.snd), (t2.fst+2 * t2.snd)-(t2.fst + t2.snd)) := by rw[h1, h2]
    _ = (t2.fst, t2.snd) := by ring
    _ = t2 := by ring
