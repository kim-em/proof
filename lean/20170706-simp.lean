structure Category :=
  ( Obj : Type )
  ( Hom : Obj → Obj → Type )
  ( identity : Π X : Obj, Hom X X )
  ( compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z )
    
structure Functor (C : Category) (D : Category) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))

definition ProductCategory (C D : Category) :
  Category :=
  {
    Obj      := C.Obj × D.Obj,
    Hom      := (λ X Y : C.Obj × D.Obj, C.Hom (X.fst) (Y.fst) × D.Hom (X.snd) (Y.snd)),
    identity := λ X, ⟨ C.identity (X.fst), D.identity (X.snd) ⟩,
    compose  := λ _ _ _ f g, (C.compose (f.fst) (g.fst), D.compose (f.snd) (g.snd))
  }

lemma Bifunctor_diagonal_identities_1
  { C : Category }
  ( F : Functor (ProductCategory C C) C )
  ( X : C.Obj )
  ( f g : C.Hom X X )
  : C.compose (@Functor.onMorphisms _ _ F (X, X) (X, X) (C.identity X, g)) (@Functor.onMorphisms _ _ F (X, X) (X, X) (f, C.identity X)) =
   @Functor.onMorphisms _ _ F (X, X) (X, X) (f, g) :=
begin
  -- simp {single_pass := tt}, -- fails with 'simplify tactic failed to simplify'
  simp {max_steps := 20},   -- fails with 'simplify failed, maximum number of steps exceeded'

  -- neither should not suffice to finish the proof!
end