open tactic
open smt_tactic
meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> try simp >> try eblast
notation `♮` := by abstract { smt_eblast }

universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)

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

@[reducible] definition CategoryOfCategoriesAndFunctors : Category := {
  Obj := Category.{u1 v1},
  Hom := λ C D, Functor C D,
  identity := λ C, IdentityFunctor C,
  compose  := λ _ _ _ F G, FunctorComposition F G,
  left_identity  := begin
                      intros,
                      dsimp, trivial
                    end
}