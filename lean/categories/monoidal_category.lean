-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor
import .natural_transformation
import .products

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

structure PreMonoidalCategory
  -- this is only for internal use: it has a tensor product, but no associator at all
  -- it's not interesting mathematically, but may allow us to introduce usable notation for the tensor product
  extends carrier : Category :=
  (tensor : Functor (carrier × carrier) carrier)
  (tensor_unit : Obj)
  (interchange: Π { A B C D E F: Obj }, Π f : Hom A B, Π g : Hom B C, Π h : Hom D E, Π k : Hom E F, 
    @Functor.onMorphisms _ _ tensor (A, D) (C, F) ((compose f g), (compose h k)) = compose (@Functor.onMorphisms _ _ tensor (A, D) (B, E) (f, h)) (@Functor.onMorphisms _ _ tensor (B, E) (C, F) (g, k)))

namespace PreMonoidalCategory
  infix `⊗`:70 := λ {C : PreMonoidalCategory} (X Y : C^.Obj),
                    Functor.onObjects C^.tensor (X, Y)
  infix `⊗m`:70 := λ {C : PreMonoidalCategory} {W X Y Z : C^.Obj}
                     (f : C^.Hom W X) (g : C^.Hom Y Z),
                     Functor.onMorphisms C^.tensor (f, g)
end PreMonoidalCategory


attribute [class] PreMonoidalCategory
attribute [instance] PreMonoidalCategory.to_Category
instance PreMonoidalCategory_coercion : has_coe PreMonoidalCategory Category := 
  ⟨PreMonoidalCategory.to_Category⟩

definition left_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor ((C × C) × C) C :=
  FunctorComposition (C^.tensor × IdentityFunctor C) C^.tensor
definition right_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × C^.tensor) C^.tensor

definition Associator ( C : PreMonoidalCategory ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C))

--print Associator
definition associator_components ( C : PreMonoidalCategory ) := Π X Y Z : C^.Obj, C^.Hom  (C^.tensor (C^.tensor (X, Y), Z)) (C^.tensor (X, C^.tensor (Y, Z)))

definition associator_to_components { C : PreMonoidalCategory } ( α : Associator C ) : associator_components C := 
begin
 exact sorry
end

/- 
-- This should be impossible to prove in general, as of course the components might not
-- satisfy naturality. I'm imagining, however, that it might be possible to write a
-- tactic that, once it has seen the actual components, blasts naturality...
-/
definition associator_from_components { C: PreMonoidalCategory } ( α : associator_components C ) : Associator C :=
  begin
    exact sorry
  end

structure LaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  --(associator' : Associator carrier)
  (associator : Π (X Y Z : Obj),
     Hom (tensor (tensor (X, Y), Z)) (tensor (X, tensor (Y, Z)))) 

-- Why can't we use notation here? It seems with slightly cleverer type checking it should work.
-- If we really can't make this work, remove PreMonoidalCategory, as it's useless.

-- TODO actually, express the associator as a natural transformation!
/- I tried writing the pentagon, but it doesn't type check. :-(
  (pentagon : Π (A B C D : Obj),
     -- we need to compare:
     -- ((AB)C)D ---> (A(BC))D ---> A((BC)D) ---> A(B(CD))
     -- ((AB)C)D ---> (AB)(CD) ---> A(B(CD))
     compose
       (compose
         (tensor <$> (associator A B C, identity D))
         (associator A (tensor (B, C)) D)
       ) (tensor <$> (identity A, associator B C D)) =
     compose
       (associator (tensor (A, B)) C D)
       (associator A B (tensor (C, D)))

  )
-/
/-
-- TODO (far future)
-- One should prove the first substantial result of this theory: that any two ways to reparenthesize are equal.
-- It requires introducing a representation of a reparathesization, but the proof should then be an easy induction.
-- It's a good example of something that is so easy for humans, that is better eventually be easy for the computer too!
-/

-- Notice that LaxMonoidalCategory.tensor has a horrible signature...
-- It sure would be nice if it read ... Functor (carrier × carrier) carrier
-- print LaxMonoidalCategory

attribute [class] LaxMonoidalCategory
attribute [instance] LaxMonoidalCategory.to_PreMonoidalCategory
instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory PreMonoidalCategory :=
  ⟨LaxMonoidalCategory.to_PreMonoidalCategory⟩


structure OplaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  -- TODO better name? unfortunately it doesn't yet make sense to say 'inverse_associator'.
  (backwards_associator : Π (X Y Z : Obj),
     Hom (tensor (X, tensor (Y, Z)))  (tensor (tensor (X, Y), Z)))

attribute [class] OplaxMonoidalCategory
attribute [instance] OplaxMonoidalCategory.to_PreMonoidalCategory
instance OplaxMonoidalCategory_coercion : has_coe OplaxMonoidalCategory PreMonoidalCategory :=
  ⟨OplaxMonoidalCategory.to_PreMonoidalCategory⟩

structure MonoidalCategory
  extends LaxMonoidalCategory, OplaxMonoidalCategory :=
  (associators_inverses_1: Π (X Y Z : Obj), compose (associator X Y Z) (backwards_associator X Y Z) = identity (tensor (tensor (X, Y), Z)))
  (associators_inverses_2: Π (X Y Z : Obj), compose (backwards_associator X Y Z) (associator X Y Z) = identity (tensor (X, tensor (Y, Z))))

attribute [class] MonoidalCategory
attribute [instance] MonoidalCategory.to_LaxMonoidalCategory
instance MonoidalCategory_coercion_to_LaxMonoidalCategory : has_coe MonoidalCategory LaxMonoidalCategory := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩
--instance MonoidalCategory_coercion_to_OplaxMonoidalCategory : has_coe MonoidalCategory OplaxMonoidalCategory := ⟨MonoidalCategory.to_OplaxMonoidalCategory⟩


namespace notations
  infix `⊗`:70 := λ {C : MonoidalCategory} (X Y : C^.Obj),
                    C^.tensor (X, Y)
  infix `⊗`:70 := λ {C : MonoidalCategory} {W X Y Z : C^.Obj}
                     (f : C^.Hom W X) (g : C^.Hom Y Z),
                     C^.tensor <$> (f, g)
end notations

definition tensor_on_left (C: MonoidalCategory) (Z: C^.Obj) : Functor C C :=
  {
    onObjects := λ X, Z ⊗ X,
    onMorphisms := --λ _ _ f, (C^.identity Z) ⊗ f,
                   --λ _ _ f, C^.tensor <$> (C^.identity Z, f),
                   --λ _ _ f, onMorphisms (C^.tensor) (C^.identity Z f),
                   λ X Y f, @Functor.onMorphisms _ _ (C^.tensor) (Z, X) (Z, Y) (C^.identity Z, f),
    identities := begin
                    intros,
                    pose H := Functor.identities (C^.tensor) (Z, X),
                    -- these next two steps are ridiculous... surely we shouldn't have to do this.
                    assert ids : Category.identity C = MonoidalCategory.identity C, blast,
                    rewrite ids,
                    exact H -- blast doesn't work here?!
                  end,
    functoriality := begin
                       intros,
                       -- similarly here
                       assert composes : Category.compose C = MonoidalCategory.compose C, blast, 
                       rewrite composes,
                       rewrite - C^.interchange,
                       rewrite C^.left_identity
                     end
  }


structure BraidedMonoidalCategory
  extends parent: MonoidalCategory :=
  (braiding: NaturalIsomorphism (tensor) (FunctorComposition (SwitchProductCategory parent parent) tensor))

-- Coercion of a NaturalIsomorphism to a NaturalTransformation doesn't seem to work. :-(

structure SymmetricMonoidalCategory
  extends parent: BraidedMonoidalCategory :=
  (symmetry: vertical_composition_of_NaturalTransformations braiding^.morphism braiding^.morphism = IdentityNaturalTransformation (IdentityFunctor (parent × parent)))

end tqft.categories.monoidal_category
