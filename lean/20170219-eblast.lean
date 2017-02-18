-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

open tactic
open smt_tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_command attribute.register `pointwise_attribute

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply) <|> any_apply cs

meta def smt   : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch >> try simp

meta def pointwise (and_then : tactic unit) : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   try (any_apply cs >> and_then)

attribute [pointwise] funext

meta def blast : tactic unit := smt >> pointwise (repeat_at_most 2 blast) -- pointwise equality of functors creates two goals

notation `♮` := by abstract { blast }

@[pointwise] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X^.fst, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_1 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X^.fst ) : (A, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_2 {α : Type u} {β : Type v} { X: α × β } { B : β } ( p : B = X^.snd ) : (X^.fst, B) = X := begin induction X, blast end
attribute [pointwise] subtype.eq

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α ♮ a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ ♮ p

universe variables u v u1 v1 u2 v2

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v) 
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity _) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity _) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [simp] Category.left_identity
attribute [simp] Category.right_identity

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C^.Obj } (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

attribute [simp] Functor.identities
attribute [simp] Functor.functoriality

instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F X) (G X))
  (naturality: ∀ { X Y : C^.Obj } (f : C^.Hom X Y),
     D^.compose (F^.onMorphisms f) (components Y) = D^.compose (components X) (G^.onMorphisms f))

instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C^.Obj, D^.Hom (F X) (G X),
  coe := NaturalTransformation.components }

@[reducible] definition vertical_composition_of_NaturalTransformations
  { C D : Category }
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D^.compose (α X) (β X),
    naturality := begin
                    blast,
                    begin[smt]
                      -- -- This doesn't work ("invalid expression"):
                      eblast_using [ D^.associativity, α^.naturality, β^.naturality ]
                      -- -- This does:
                      -- eblast_using [ Category.associativity, NaturalTransformation.naturality ]
                    end,
                  end
  }