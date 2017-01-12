import standard

meta def blast : tactic unit :=
using_smt $ return ()

structure Category :=
  (Obj : Type)
  (Hom : Obj -> Obj -> Type)
  (identity : Π A : Obj, Hom A A)
  (compose  : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)

  (left_identity  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (identity _) f = f)
  (right_identity : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (identity _) = f)
  (associativity  : Π ⦃A B C D : Obj⦄ (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h))

attribute [class] Category

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π ⦃A B : C^.Obj⦄,
                C^.Hom A B → D^.Hom (onObjects A) (onObjects B))
  (identities : Π (A : C^.Obj),
    onMorphisms (C^.identity A) = D^.identity (onObjects A))
  (functoriality : Π ⦃X Y Z : C^.Obj⦄ (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

attribute [class] Functor

instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

namespace Functor
  infix `<$>`:50 := λ {C : Category} {D : Category}
                      (F : Functor C D) {A B : C^.Obj} (f : C^.Hom A B),
                      onMorphisms F f
end Functor

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π A : C^.Obj, D^.Hom (F A) (G A))
  (naturality: Π { A B : C^.Obj }, Π f : C^.Hom A B, D^.compose (F <$> f) (components B) = D^.compose (components A) (G <$> f))

instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π A : C^.Obj, D^.Hom (F A) (G A),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( α β : NaturalTransformation F G )
  ( w: Π X : C^.Obj, α X = β X ) : α = β :=
  begin
    induction α,
    induction β,
    -- Argh, how to complete this proof?
    exact sorry
  end


