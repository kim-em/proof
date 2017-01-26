-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories.functor

structure { u1 v1 u2 v2 } Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π ⦃X Y : C^.Obj⦄,
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : ∀ ⦃X Y Z : C^.Obj⦄ (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

attribute [simp] Functor.identities
attribute [simp] Functor.functoriality

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

/-
-- Unfortunately we haven't been able to set up similar notation for morphisms.
-- Instead we define notation so that `F <$> f` denotes the functor `F` applied to the morphism `f`.
-- One can still write out `onMorphisms F f` when needed, or even the very verbose `@Functor.onMorphisms C D F X Y f`.
--namespace notations
  -- Lean complains about the use of local variables in
  -- notation. There must be a way around that.
  infix `<$>` :50 := λ {C : Category} {D : Category}
                       (F : Functor C D) {X Y : C^.Obj} (f : C^.Hom X Y),
                       Functor.onMorphisms F f
end notations

open notations
-/

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if to_onObjects is already in scope.
--instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
--{ F   := λ f, Π ⦃X Y : C^.Obj⦄, C^.Hom X Y → D^.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

@[reducible] definition IdentityFunctor ( C: Category ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := λ _, rfl,
  functoriality := λ _ _ _ _ _, rfl
}

@[reducible] definition FunctorComposition { C D E : Category } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G (F X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f),
  identities    := begin
                     intros, simp
                   end,
  functoriality := begin
                     intros, simp
                   end
}

lemma FunctorComposition_onMorphisms { C D E : Category } { F : Functor C D } { G : Functor D E } { X Y : C^.Obj } { f : C^.Hom X Y } :
  (FunctorComposition F G)^.onMorphisms f = G^.onMorphisms (F^.onMorphisms f) := by blast

end tqft.categories.functor
