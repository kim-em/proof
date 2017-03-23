universe variables u v

structure Category :=
  (Obj : Sort u)
  (Hom : Obj → Obj → Sort v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f)

attribute [simp] Category.left_identity
attribute [simp] Category.right_identity

universe variables u1 v1 u2 v2 u3 v3

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F^.onObjects X) (G^.onObjects X))
  (naturality: ∀ { X Y : C^.Obj } (f : C^.Hom X Y),
     D^.compose (F^.onMorphisms f) (components Y) = D^.compose (components X) (G^.onMorphisms f))

set_option pp.universes true
#check NaturalTransformation

definition IdentityNaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) : NaturalTransformation F F :=
  {
    components := λ X, D^.identity (F^.onObjects X),
    naturality := begin intros, simp end
  }
#check IdentityNaturalTransformation