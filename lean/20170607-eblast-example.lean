structure Category :=
  ( Obj : Type )
  ( Hom : Obj → Obj → Type )
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [ematch] Category.associativity

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
  (functoriality : ∀ { X Y Z : C.Obj } (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))

attribute [simp,ematch] Functor.functoriality

instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C.Obj → D.Obj,
  coe := Functor.onObjects }

structure NaturalTransformation { C : Category } { D : Category } ( F G : Functor C D ) :=
  (components: Π X : C.Obj, D.Hom (F X) (G X))
  (naturality: ∀ { X Y : C.Obj } (f : C.Hom X Y),
     D.compose (F.onMorphisms f) (components Y) = D.compose (components X) (G.onMorphisms f))

attribute [ematch] NaturalTransformation.naturality

meta def unfold_coe : tactic unit := tactic.dunfold [ ``has_coe_to_fun.coe ]

definition vertical_composition_of_NaturalTransformations
  { C : Category } { D : Category } 
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D.compose (α.components X) (β.components X),
    naturality := begin[smt]
                    intros,
                    unfold_coe,
                    eblast
                  end
  }