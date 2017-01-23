-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor
import .natural_transformation

open tqft.categories
open tqft.categories.functor

namespace tqft.categories.products

definition ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd)),
    compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

    left_identity  := begin
                        intros,
                        rewrite [ C^.left_identity, D^.left_identity ],
                        induction f,
                        simp
                      end,
    right_identity := begin
                        intros,
                        rewrite [ C^.right_identity, D^.right_identity],
                        induction f,
                        simp
                      end,
    associativity  := begin
                        intros,
                        rewrite [ C^.associativity, D^.associativity ]
                      end
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

-- These seem extremely tedious.
lemma product_identity_fst { C D : Category } { X : (C × D)^.Obj } : ((C × D)^.identity X)^.fst = C^.identity X^.fst := by blast
lemma product_identity_snd { C D : Category } { X : (C × D)^.Obj } : ((C × D)^.identity X)^.snd = D^.identity X^.snd := by blast

lemma product_identity { C D : Category } { X : C^.Obj } { Y : D^.Obj } : (C × D)^.identity (X, Y) = (C^.identity X, D^.identity Y) := by blast

lemma product_compose { C D : Category } { X Y Z : (C × D)^.Obj } { f : (C × D)^.Hom X Y } { g : (C × D)^.Hom Y Z }: (C × D)^.compose f g = (C^.compose f^.fst g^.fst, D^.compose f^.snd g^.snd) := by blast 

lemma product_compose' { C D : Category } { U V W : C^.Obj } { X Y Z : D^.Obj } { f : C^.Hom U V } { g : C^.Hom V W } { h : D^.Hom X Y } { k : D^.Hom Y Z } :
  @Category.compose (C × D) (U, X) (V, Y) (W, Z) (f, h) (g, k) = (C^.compose f g, D^.compose h k) := by blast

definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects := λ X, (F X^.fst, G X^.snd),
  onMorphisms := λ _ _ f, (F^.onMorphisms f^.fst, G^.onMorphisms f^.snd),
  identities := begin
                  intros X,
                  rewrite product_identity_fst,
                  rewrite product_identity_snd,
                  rewrite F^.identities,
                  rewrite G^.identities,
                  rewrite product_identity                              
                end,
  functoriality := begin
                     intros X Y Z f g,
                     rewrite product_compose, 
                     rewrite product_compose', 
                     rewrite F^.functoriality, 
                     rewrite G^.functoriality
                   end
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := begin -- seems a shame that blast can't do intros itself
                     intros, blast
                   end,
  functoriality := begin
                     intros, blast
                   end
}

definition ProductCategoryAssociator ( C D E : Category ) : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := begin
                     intros, blast 
                   end,
  functoriality := begin
                     intros, blast
                   end
}

end tqft.categories.products

