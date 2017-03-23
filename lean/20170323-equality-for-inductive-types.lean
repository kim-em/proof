open tactic
open smt_tactic


meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> try simp >> try eblast



meta def blast  : tactic unit := intros >> try dsimp >> try simp >> try smt_eblast

-- In a timing test on 2017-02-18, I found that using `abstract { blast }` instead of just `blast` resulted in a 5x speed-up!
notation `♮` := by abstract { blast }

universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

universe variables u1 v1 u2 v2 u3 v3

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C^.Obj } (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))


attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

@[reducible] definition IdentityFunctor ( C: Category.{u1 v1} ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := ♮,
  functoriality := ♮
}

@[reducible] definition FunctorComposition { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G^.onObjects (F^.onObjects X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f),
  identities    := ♮,
  functoriality := ♮
}