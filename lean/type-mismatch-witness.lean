structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type) 

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

lemma Functors_pointwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X ) 
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, F^.onMorphisms f == G^.onMorphisms f ) : F = G :=
  begin

  end
