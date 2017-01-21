-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor
import .natural_transformation

open tqft.categories
open tqft.categories.notations
open tqft.categories.functor
open tqft.categories.functor.notations

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

definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects := λ X, (F X^.fst, G X^.snd),
  onMorphisms := λ _ _ f, (F <$> f^.fst, G <$> f^.snd),
  identities := begin
                  intros o,
                  induction o,
                  pose hF := F^.identities fst,
                  pose hG := G^.identities snd,                  
                  exact sorry
                end,
  functoriality := begin
                     intros,
                     exact sorry
                   end
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := sorry, -- I thought these used to work by blast
  functoriality := sorry
}

definition ProductCategoryAssociator ( C D E : Category ) : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := sorry,
  functoriality := sorry
}

end tqft.categories.products

