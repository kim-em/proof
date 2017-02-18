open tactic
open smt_tactic

meta def blast : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch >> try simp

universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v) 
  (identity : Π X : Obj, Hom X X)
    
universe variables u1 v1 u2 v2

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))

instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

@[reducible] definition ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd))
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

structure MonoidalCategory extends carrier : Category :=
  (tensor : Functor (carrier × carrier) carrier)

instance MonoidalCategory_coercion : has_coe MonoidalCategory Category := 
  ⟨MonoidalCategory.to_Category⟩

definition tensor_on_left (C: MonoidalCategory.{u v}) (Z: C^.Obj) : Functor.{u v u v} C C :=
  {
    onObjects := λ X, C^.tensor (Z, X),
    onMorphisms := λ X Y f, @Functor.onMorphisms _ _ (C^.tensor) (Z, X) (Z, Y) (C^.identity Z, f),
    identities := begin
                    intros, 
                    -- these next two steps are ridiculous... surely we shouldn't have to do this.
                    assert ids : Category.identity.{u v} C = MonoidalCategory.identity C, blast,
                    rewrite ids,
                    rewrite Functor.identities (C^.tensor)            
                  end
  }
