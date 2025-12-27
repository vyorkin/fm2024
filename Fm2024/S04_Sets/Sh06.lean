/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

namespace S04Sh06

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x hxs
  rw [Set.image, Set.preimage]
  use x, hxs -- x ∈ {x | f x ∈ {x | f x = x}}

example : f '' (f ⁻¹' T) ⊆ T := by
  rw [Set.image]
  intro y ⟨x, hx, hxeq⟩
  rw [Set.preimage] at hx
  rw [← hxeq]
  exact hx

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h x xs
    exact h ⟨x, xs, rfl⟩
  · intro hs y ⟨x, xs, hxeq⟩
    rw [← hxeq]
    exact hs xs

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  rw [Set.preimage]
  simp

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  constructor
  · rintro ⟨x, hxs, rfl⟩
    assumption
  · intro h
    use x
    constructor
    · exact h
    · rfl

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  constructor
  · intro h
    unfold Function.comp at *
    repeat rw [Set.preimage] at *
    exact h
  · intro h; exact h

example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by rfl

example : g ∘ f '' S = g '' (f '' S) := by
  ext x; constructor
  · intro ⟨x, hxs, hxeq⟩
    unfold Set.image at *
    unfold Function.comp at hxeq
    rw [← hxeq]
    use f x
    constructor
    · use x, hxs
    · rfl
  · rintro ⟨x, his, rfl⟩
    obtain ⟨y, hys, hyeq⟩ := his
    unfold Set.image
    use y
    rw [← hyeq]
    rw [Function.comp]
    exact ⟨hys, rfl⟩

end S04Sh06
