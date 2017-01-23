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
  (naturality: ∀ { X Y : C^.Obj } (f : C^.Hom X Y),
     D^.compose (F^.onMorphisms f) (components Y) = D^.compose (components X) (G^.onMorphisms f))

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C^.Obj, D^.Hom (F X) (G X),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( α β : NaturalTransformation F G )
  ( w : ∀ X : C^.Obj, α X = β X ) : α = β :=
  begin
    induction α with αc,
    induction β with βc,
    have hc : αc = βc, from funext w,
    by subst hc
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
    components := λ X : C^.Obj, E^.compose (β (F X)) (I^.onMorphisms (α X)),
    naturality := begin
                    intros,
                    rewrite - β^.naturality,
                    rewrite - β^.naturality,
                    rewrite FunctorComposition_onMorphisms,
                    rewrite FunctorComposition_onMorphisms, 
                    -- I'm stuck for now. It seems either of the next two tactics should apply, but both give errors.
                    -- rewrite E^.associativity,
                    -- rewrite - E^.associativity,
                    exact sorry
                  end
  }

-- To define a natural isomorphism, we'll define the functor category, and ask for an isomorphism there.
-- It's then a lemma that each component is an isomorphism, and vice versa.

@[simp]
lemma vertical_composition_of_NaturalTransformations_components 
  { C D : Category }
  { F G H : Functor C D }
  { α : NaturalTransformation F G }
  { β : NaturalTransformation G H }
  { X : C^.Obj } :
  (vertical_composition_of_NaturalTransformations α β)^.components X = D^.compose (α^.components X) (β^.components X) := by blast

@[simp]
lemma IdentityNaturalTransformation_components
  { C D : Category }
  { F : Functor C D }
  { X : C^.Obj } :
  (IdentityNaturalTransformation F)^.components X = D^.identity (F X) := by blast

definition FunctorCategory ( C D : Category ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D,

  left_identity  := begin
                     intros,
                     apply NaturalTransformations_componentwise_equal,
                     intros,
                     blast, -- what is blast actually doing here? it's helpful, but only for a little step.
                     simp [ D^.left_identity ]
                     /-
                     -- This 'simp' applies the lemmas above, effectively implementing:
                     -- rewrite vertical_composition_of_NaturalTransformations_components,
                     -- rewrite IdentityNaturalTransformation_components,
                     -- rewrite D^.left_identity
                     -/
                     -- TODO: How can be mark D^.left_identity as automatically available for `simp`?
                    end, 
  right_identity := 
                   /- 
                   -- This is just a copy and paste of the proof for left_identity.
                   -- Eventually of course this is unacceptable, and demands appropriate tactics.
                   -/
                   begin 
                     intros,
                     apply NaturalTransformations_componentwise_equal,
                     intros, 
                     blast,
                     simp [ D^.right_identity ]
                    end, 
  associativity  := begin
                      intros,
                      apply NaturalTransformations_componentwise_equal,
                      intros,
                      blast,
                      simp [ D^.associativity ]
                    end
}

definition NaturalIsomorphism { C D : Category } ( F G : Functor C D ) := Isomorphism (FunctorCategory C D) F G

-- It's a pity we need to separately define this coercion.
-- Ideally the coercion from Isomorphism along .morphism would just apply here.
-- Somehow we want the definition above to be more transparent?
instance NaturalIsomorphism_coercion_to_NaturalTransformation { C D : Category } { F G : Functor C D } : has_coe (NaturalIsomorphism F G) (NaturalTransformation F G) :=
  { coe := Isomorphism.morphism }

open NaturalTransformation

-- Getting this coercion to work is really painful. We shouldn't have to write
--     @components C D F G α X
-- below, but rather just:
--     α X
-- or at least
--     α^.components X

lemma components_of_NaturalIsomorphism_are_isomorphisms { C D : Category } { F G : Functor C D } { α : NaturalIsomorphism F G } { X : C^.Obj } :
 Inverse (@components C D F G α X) := 
  {
    inverse := α^.inverse^.components X,
    witness_1 := α^.witness_1, -- TODO we need to evaluate both sides of this equation at X.
    witness_2 := sorry
  }

end tqft.categories.natural_transformation
