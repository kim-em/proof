-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

@[simp]
lemma add_left_cancel_iff' (a b : ℕ) : a + b = a ↔ b = 0 :=
@add_left_cancel_iff _ _ a b 0

@[simp]
lemma add_right_cancel_iff' (a b : ℕ) : a + b = b ↔ a = 0 :=
begin
  note h := @add_right_cancel_iff _ _ b a 0,
  simp at h,
  exact h
end

@[simp] lemma f ( α : Type ) [ i : inhabited α ] ( p : Prop ) : (α → p) ↔ p := sorry

definition e : { n : ℕ // (∀ f : ℕ, n + f = f) ∧ (∀ f : ℕ, f + n = f) } :=
begin
  simp,
  exact ⟨ 0, rfl ⟩
end