structure {u v} Category :=
  ( Obj : Type u )
  ( Hom : Obj → Obj → Type v )
  ( identity : Π X : Obj, Hom X X )
  ( compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z )

  ( left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f )
  ( right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f )
  ( associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )
    
structure {u1 v1 u2 v2} Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C.Obj),
    onMorphisms (C.identity X) = D.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C.Obj } (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))

definition {u1 v1 u2 v2 u3 v3} FunctorComposition { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G.onObjects (F.onObjects X),
  onMorphisms   := λ _ _ f, G.onMorphisms (F.onMorphisms f),
  identities    := sorry,
  functoriality := sorry
}

structure {u1 v1 u2 v2} NaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F G : Functor C D ) :=
  (components: Π X : C.Obj, D.Hom (F.onObjects X) (G.onObjects X))
  (naturality: ∀ { X Y : C.Obj } (f : C.Hom X Y),
     D.compose (F.onMorphisms f) (components Y) = D.compose (components X) (G.onMorphisms f))

definition {u1 v1 u2 v2 u3 v3} horizontal_composition_of_NaturalTransformations
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  { H I : Functor D E }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
  {
    components := λ X : C.Obj, E.compose (β.components (F.onObjects X)) (I.onMorphisms (α.components X)),
    naturality := begin intros, unfold_projs, end
  }