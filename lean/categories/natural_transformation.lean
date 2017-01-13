-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor

open tqft.categories
open tqft.categories.functor

namespace tqft.categories.natural_transformation

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F X) (G X))
  (naturality: Π { X Y : C^.Obj }, Π f : C^.Hom X Y, D^.compose (F <$> f) (components Y) = D^.compose (components X) (G <$> f))

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C^.Obj, D^.Hom (F X) (G X),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( α β : NaturalTransformation F G )
  ( w: Π X : C^.Obj, α X = β X ) : α = β :=
  begin
    induction α,
    induction β,
    -- Argh, how to complete this proof?
    exact sorry
  end

definition IdentityNaturalTransformation { C D : Category } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D^.identity (F X),
    naturality := begin
                    intros,
                    rewrite [ D^.left_identity, D^.right_identity ]
                  end
  }

definition vertical_composition_of_NaturalTransformations
  { C D : Category }
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D^.compose (α X) (β X),
    naturality := begin
                    intros,
                    /- this proof was written by a sufficient stupid process that I am confident a computer
                    -- could have done it! -/
                    rewrite D^.associativity,
                    rewrite - β^.naturality,
                    rewrite - D^.associativity,
                    rewrite α^.naturality,
                    rewrite D^.associativity
                  end
  }

definition horizontal_composition_of_NaturalTransformations
  { C D E : Category }
  { F G : Functor C D }
  { H I : Functor D E } 
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (tqft.categories.functor.FunctorComposition F H) (tqft.categories.functor.FunctorComposition G I) :=
  {
    components := λ X : C^.Obj, E^.compose (β (F X)) (I <$> (α X)),
    naturality := begin
                    intros,
                    rewrite - β^.naturality,
                    rewrite - β^.naturality,
                    exact sorry -- I'm stuck here, as I don't know how to apply the definition of FunctorComposition.onMorphisms
                  end
  }

-- To define a natural isomorphism, we'll define the functor category, and ask for an isomorphism there.
-- It's then a lemma that each component is an isomorphism, and vice versa.

instance FunctorCategory ( C D : Category ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose := @vertical_composition_of_NaturalTransformations C D,

  left_identity := sorry, -- these facts all rely on NaturalTransformations_componentwise_equal above.
  right_identity := sorry,
  associativity := sorry
}

definition NaturalIsomorphism { C D : Category } ( F G : Functor C D ) := Isomorphism (tqft.categories.functor.FunctorCategory C D) F G

-- TODO I'm confused how to even say this!
--lemma components_of_NaturalIsomorphism_are_isomorphisms { C D : Category } { F G : Functor C D } ( α : NaturalIsomorphism F G ) ....?


end tqft.categories.natural_transformation
