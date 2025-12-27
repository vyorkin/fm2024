/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

namespace S04Sh05

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x; constructor
  · rintro (hxa | hxa) <;> assumption
  · intro hxa; left; assumption

example : A ∩ A = A := by
  ext x; constructor
  · intro ⟨hl, hr⟩
    assumption
  · intro ha
    exact ⟨ha, ha⟩

example : A ∩ ∅ = ∅ := by
  ext x; constructor
  · rintro ⟨ha, he⟩
    assumption
  · intro he
    tauto

example : A ∪ univ = univ := by simp

example : A ⊆ B → B ⊆ A → A = B := by
  intro hab hba
  ext x
  constructor
  · intro hxa
    exact hab hxa
  · intro hxb
    exact hba hxb

example : A ∩ B = B ∩ A := by
  ext x
  constructor
  · rintro ⟨hxa, hxb⟩
    exact ⟨hxb, hxa⟩
  · rintro ⟨hxb, hxa⟩
    exact ⟨hxa, hxb⟩

example : A ∩ B = B ∩ A :=
  Subset.antisymm
  (fun _ ⟨hxa, hxb⟩ ↦ ⟨hxb, hxa⟩ )
  (fun _ ⟨hxb, hxa⟩ ↦ ⟨hxa, hxb⟩)

example : A ∩ (B ∩ C) = A ∩ B ∩ C :=
  Subset.antisymm
  (fun _ ⟨hxa, ⟨hxb, hxc⟩⟩ ↦ ⟨⟨hxa, hxb⟩, hxc⟩)
  (fun _ ⟨⟨hxa, hxb⟩, hxc⟩ ↦ ⟨hxa, ⟨hxb, hxc⟩⟩)

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x; constructor
  · rintro (hxa | (hxb | hxc))
    · left; left; exact hxa
    · left; right; exact hxb
    · right; exact hxc
  · rintro ((hxa | hxb) | hxc)
    · left; exact hxa
    · right; left; exact hxb
    · right; right; exact hxc

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) :=
  Subset.antisymm
    (fun x (hab : x ∈ A ∪ (B ∩ C)) =>
      Or.elim hab
        (fun ha => ⟨Or.inl ha, Or.inl ha⟩)
        (fun ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩))
    (fun _ ⟨hab, hac⟩ =>
      Or.elim hab
        (fun ha => Or.inl ha)
        (fun hb =>
          Or.elim hac
            (fun ha => Or.inl ha)
            (fun hc => Or.inr ⟨hb, hc⟩)))

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · exact ⟨Or.inl ha, Or.inl ha⟩
    · exact ⟨Or.inr hb, Or.inr hc⟩
  · rintro ⟨hab, hac⟩
    show x ∈ A ∪ (B ∩ C)
    rcases hab with ha | hb
    · left
      exact ha
    · rcases hac with ha | hc
      · left
        exact ha
      · right
        exact ⟨hb, hc⟩

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  · rintro ⟨ha, hb | hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hc⟩

end S04Sh05
