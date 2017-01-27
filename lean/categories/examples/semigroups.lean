-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category

namespace tqft.categories.examples.semigroups

open tqft.categories

set_option pp.universes true

structure semigroup_morphism { α β : Type } ( s : semigroup α ) ( t: semigroup β ) :=
  (map: α → β)
  (multiplicative : ∀ x y : α, map(x * y) = map(x) * map(y))

attribute [simp] semigroup_morphism.multiplicative

-- This defines a coercion so we can write `f x` for `map f x`.
instance monoid_semigroup_to_map { α β : Type } { s : semigroup α } { t: semigroup β } : has_coe_to_fun (semigroup_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := semigroup_morphism.map }

@[reducible] definition semigroup_identity { α : Type } ( s: semigroup α ) : semigroup_morphism s s :=
{
  map := id,
  multiplicative := ♮
}

@[reducible] definition semigroup_morphism_composition
  { α β γ : Type } { s: semigroup α } { t: semigroup β } { u: semigroup γ}
  ( f: semigroup_morphism s t ) ( g: semigroup_morphism t u ) : semigroup_morphism s u :=
{
  map := λ x, g (f x),
  multiplicative := begin blast, simp end
}

lemma semigroup_morphism_pointwise_equality
  { α β : Type } { s : semigroup α } { t: semigroup β }
  ( f g : semigroup_morphism s t )
  ( w : ∀ x : α, f x = g x) : f = g :=
/-
-- This proof is identical to that of the lemma NaturalTransformations_componentwise_equal.
-- TODO: automate!
-/
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc, from funext w,
    by subst hc
end

definition CategoryOfSemigroups : Category := 
{
    Obj := Σ α : Type, semigroup α,
    Hom := λ s t, semigroup_morphism s.2 t.2,

    identity := λ s, semigroup_identity s.2,
    compose  := λ _ _ _ f g, semigroup_morphism_composition f g,

    /-
    -- These proofs are a bit tedious, how do we automate?
    -/
    left_identity  := begin intros, apply semigroup_morphism_pointwise_equality, blast end,
    right_identity := begin intros, apply semigroup_morphism_pointwise_equality, blast end,
    associativity  := ♮
}

end tqft.categories.examples.semigroups
