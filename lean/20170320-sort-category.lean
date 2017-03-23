-- This is an example illustrating a problem with unification when using Category based on Sort, rather than Type.

-- We set up some tactics:
open tactic
open smt_tactic
meta def smt_eblast : tactic unit := using_smt $ try eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch
meta def blast  : tactic unit := intros >> try dsimp >> try simp >> try smt_eblast
notation `♮` := by abstract { blast }

attribute [reducible] cast

@[reducible] def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α (by smt_ematch) a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ (by smt_ematch) p

-- And now a minimal example:
universe variables u v

structure Category :=
  (Obj : Sort u)
  (Hom : Obj → Obj → Sort v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f)

attribute [simp] Category.left_identity

universe variables u1 v1 u2 v2

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

set_option pp.all true

def rewriteMorphism   { C : Category.{u1 v1} }
  { D : Category.{u2 v2} } 
  { F G : Functor C D } 
  { X Y : C^.Obj }
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
  ( f : D^.Hom (F^.onObjects X) (F^.onObjects Y) ) : D^.Hom (G^.onObjects X) (G^.onObjects Y) :=
  begin
    rewrite (objectWitness X) at f,
    rewrite (objectWitness Y) at f,
    exact f
  end

lemma Functors_pointwise_equal
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} } 
  { F G : Functor C D } 
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X ) 
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, rewriteMorphism objectWitness (F^.onMorphisms f)  = G^.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  subst h_objects,
  assert h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact morphismWitness X Y f,
  subst h_morphisms
end

@[reducible] definition IdentityFunctor ( C: Category ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f
}

@[reducible] definition FunctorComposition { C D E : Category } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G^.onObjects (F^.onObjects X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f)
}


definition CategoryOfCategoriesAndFunctors : Category := {
  Obj := Category,
  Hom := λ C D, Functor C D,
  identity := λ C, IdentityFunctor C,
  compose  := λ _ _ _ F G, FunctorComposition F G,
  left_identity  := begin
                      intros,
                      fapply Functors_pointwise_equal,
                      intros,
                      dsimp,
                      refl,
                      intros,
                      dsimp,
                      refl
                    end
}