/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

namespace S04Sh03

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro hna
  exact hna

example : x ∉ A → x ∈ A → False := id

example : x ∈ A → x ∉ A → False := by
  intro ht
  by_contra hf
  contradiction

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hab hxnb
  contrapose! hxnb with hxa
  exact hab hxa

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro hxe
  change False at hxe
  exact hxe

example : x ∉ (∅ : Set X) := by
  intro hxe
  exfalso
  assumption

example : x ∈ Aᶜ → x ∉ A := by
  intro h
  assumption

-- 1)
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hxa hexac
    obtain ⟨x, hxac⟩ := hexac
    specialize hxa x
    contradiction
  · intro hnexac x
    contrapose! hnexac
    use x
    exact hnexac

-- 2)
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hxa hexac
    obtain ⟨x, hxac⟩ := hexac
    specialize hxa x
    contradiction
  · intro hnexac x
    by_contra hxna
    apply hnexac
    use x
    exact hxna

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · rintro ⟨x, hxa⟩
    contrapose! hxa
    exact hxa x
  · intro hnaxac
    contrapose! hnaxac
    exact hnaxac

end S04Sh03
