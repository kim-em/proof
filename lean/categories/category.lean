-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

-- Lean's SMT tactic isn't yet hooked up by default. This snippet makes 'blast' available as an all purpose tactic.
meta def blast : tactic unit := using_smt $ return ()

/-
-- We've decided that Obj and Hom should be fields of Category, rather than parameters.
-- Mostly this is for the sake of simpler signatures, but it's possible that it is not the right choice.
-- Functor and NaturalTransformation are each parameterized by both their source and target.
-/

namespace tqft.categories

structure Category :=
  (Obj : Type)
  (Hom : Obj -> Obj -> Type)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π ⦃X Y Z : Obj⦄, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ ⦃X Y : Obj⦄ (f : Hom X Y), compose (identity _) f = f)
  (right_identity : ∀ ⦃X Y : Obj⦄ (f : Hom X Y), compose f (identity _) = f)
  (associativity  : ∀ ⦃W X Y Z : Obj⦄ (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [class] Category
/-
-- Unfortunately declaring Category as a class when it is first declared results
-- in an unexpected type signature; this is a feature, not a bug, as Stephen discovered
-- and explained at https://github.com/semorrison/proof/commit/e727197e794647d1148a1b8b920e7e567fb9079f
--
-- We just declare things as structures, and then add the class attribute afterwards.
-/

-- Ugh. notation is a reserved word.
namespace notations
  infixr `∘`     := Category.compose _ 
  infixl `⟶` :25 := Category.Hom _ 
end notations

open notations

structure Isomorphism ( C: Category ) ( X Y : C^.Obj ) :=
  (morphism : C^.Hom X Y)
  (inverse : C^.Hom Y X)
  (witness_1 : morphism ∘ inverse = C^.identity X)
  (witness_2 : inverse ∘ morphism = C^.identity Y)

instance Isomorphism_coercion_to_morphism { C : Category } { X Y : C^.Obj } : has_coe (Isomorphism C X Y) (C^.Hom X Y) :=
  { coe := Isomorphism.morphism }

end tqft.categories
