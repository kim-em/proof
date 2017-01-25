-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..functor
import ..natural_transformation
import ..products
import ..monoidal_category

namespace tqft.categories.examples.monoids

open tqft.categories

set_option pp.universes true

structure monoid_morphism { α β : Type } ( s : monoid α ) ( t: monoid β ) :=
  (map: α → β)
  (multiplicativity : ∀ x y : α, map(x * y) = map(x) * map(y))

attribute [simp] monoid_morphism.multiplicativity

-- This defines a coercion so we can write `f x` for `map f x`.
instance monoid_morphism_to_map { α β : Type } { s : monoid α } { t: monoid β } : has_coe_to_fun (monoid_morphism s t) :=
{ F   := λ f, Π x : α, β,
  coe := monoid_morphism.map }

definition monoid_identity { α : Type } ( s: monoid α ) : monoid_morphism s s :=
{
  map := id,
  multiplicativity := begin intros, blast end
}

definition monoid_morphism_composition
  { α β γ : Type } { s: monoid α } { t: monoid β } { u: monoid γ}
  ( f: monoid_morphism s t ) ( g: monoid_morphism t u ) : monoid_morphism s u :=
{
  map := λ x, g (f x),
  multiplicativity := begin intros, blast, simp end
}

lemma monoid_morphism_pointwise_equality
  { α β : Type } { s : monoid α } { t: monoid β }
  ( f g : monoid_morphism s t )
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

instance CategoryOfMonoids : Category := 
{
    Obj := Σ α : Type, monoid α,
    Hom := λ s t, monoid_morphism s.2 t.2,

    identity := λ s, monoid_identity s.2,
    compose  := λ _ _ _ f g, monoid_morphism_composition f g,

    /-
    -- These proofs are a bit tedious, how do we automate?
    -/
    left_identity  := begin intros, apply monoid_morphism_pointwise_equality, intros, dsimp [monoid_identity, monoid_morphism_composition], blast end,
    right_identity := begin intros, apply monoid_morphism_pointwise_equality, intros, dsimp [monoid_identity, monoid_morphism_composition], blast end,
    associativity  := begin intros, apply monoid_morphism_pointwise_equality, intros, dsimp [monoid_morphism_composition], blast end
}

end tqft.categories.examples.monoids
