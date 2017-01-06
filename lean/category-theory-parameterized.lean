import standard

meta def blast : tactic unit :=
using_smt $ return ()

structure Category (Obj : Type) (Hom : Obj -> Obj -> Type) :=
  (identity : Π A : Obj, Hom A A)
  (compose  : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)

  (left_identity  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (identity _) f = f)
  (right_identity : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (identity _) = f)
  (associativity  : Π ⦃A B C D : Obj⦄ (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h))

attribute [class] Category
-- declaring it as a class from the beginning results in an insane
-- signature ... This really seems like it must be a bug, or at least
-- a rough edge.
-- print Category

instance ℕCategory : Category unit (λ a b, ℕ) :=
  { identity := λ a, 0,
    compose  := λ a b c, add,

    left_identity  := λ a b, zero_add,
      -- Sadly, "by blast" doesn't work here. I think this is because
      -- "by blast" checks if the heads of the expressions match,
      -- which is the case for right_identity and associativity, but
      -- not left_identity.
    right_identity := by blast, --λ a b, add_zero,
    associativity  := by blast  --λ a b c d, add_assoc
  }

open Category

variables { Obj₁ Obj₂ : Type }
variables { Hom₁ : Obj₁ → Obj₁ → Type } { Hom₂ : Obj₂ → Obj₂ → Type }

structure Functor (C₁ : Category Obj₁ Hom₁) (C₂ : Category Obj₂ Hom₂) :=
  (onObjects   : Obj₁ → Obj₂)
  (onMorphisms : Π ⦃A B : Obj₁⦄,
                Hom₁ A B → Hom₂ (onObjects A) (onObjects B))
  (identities : Π (A : Obj₁),
    onMorphisms (identity C₁ A) = identity C₂ (onObjects A))
  (functoriality : Π ⦃A B C : Obj₁⦄ (f : Hom₁ A B) (g : Hom₁ B C),
    onMorphisms (compose C₁ f g) = compose C₂ (onMorphisms f) (onMorphisms g))

attribute [class] Functor

namespace Functor
  -- Lean complains about the use of local variables in
  -- notation. There must be a way around that.
  infix `<$>`:50 := λ {Obj₁ Obj₂ : Type} {Hom₁ : Obj₁ → Obj₁ → Type}
                      {Hom₂ : Obj₂ → Obj₂ → Type}
                      {C₁ : Category Obj₁ Hom₁} {C₂ : Category Obj₂ Hom₂}
                      (F : Functor C₁ C₂) (A : Obj₁),
                      onObjects F A
  infix `<$>m`:50 := λ {Obj₁ Obj₂ : Type} {Hom₁ : Obj₁ → Obj₁ → Type}
                      {Hom₂ : Obj₂ → Obj₂ → Type}
                      {C₁ : Category Obj₁ Hom₁} {C₂ : Category Obj₂ Hom₂}
                      (F : Functor C₁ C₂) {A B : Obj₁} (f : Hom₁ A B),
                      onMorphisms F f
end Functor

--print Functor

instance DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ A B n, n + n),
      -- Sadly, "by blast" doesn't work below if we replace "n + n"
      -- with "2 * n".  Again, I think this is because the heads don't
      -- match. If you use "n * 2", then identities works by blast,
      -- but functoriality still doesn't.
    identities    := by blast,
    functoriality := by blast
  }

variables { Obj_C Obj_D : Type }
variables { Hom_C : Obj_C -> Obj_C -> Type } { Hom_D : Obj_D -> Obj_D -> Type }

open prod

instance ProductCategory (C : Category Obj_C Hom_C) (D : Category Obj_D Hom_D) :
  Category (Obj_C × Obj_D) (λ a b, Hom_C (fst a) (fst b) × Hom_D (snd a) (snd b)) :=
  {
    identity := λ a, (identity C (fst a), identity D (snd a)),
    compose  := λ a b c f g, (compose C (fst f) (fst g), compose D (snd f) (snd g)),

    left_identity  := begin
                        intros,
                        pose x := left_identity C (fst f),
                        pose y := left_identity D (snd f),
                        induction f,
                        blast
                      end,
    right_identity := begin
                        intros,
                        pose x := right_identity C (fst f),
                        pose y := right_identity D (snd f),
                        induction f,
                        blast
                      end,
    associativity  := begin
                        intros,
                        pose x := associativity C (fst f) (fst g) (fst h),
                        pose y := associativity D (snd f) (snd g) (snd h),
                        induction f,
                        blast
                      end
  }

namespace ProductCategory
  notation C `×c` D := ProductCategory C D
end ProductCategory

def ℕTensorProduct : Functor (ℕCategory ×c ℕCategory) ℕCategory :=
  { onObjects     := fst,
    onMorphisms   := λ A B n, fst n + snd n,
    identities    := by blast,
    functoriality := by blast
  }

structure LaxMonoidalCategory (Obj : Type) (Hom : Obj → Obj → Type)
  extends carrier : Category Obj Hom :=
  (tensor : Functor (carrier ×c carrier) carrier)
  (unit : Obj)

  (associator : Π (A B C : Obj),
     Hom (tensor <$> (tensor <$> (A, B), C)) (tensor <$> (A, tensor <$> (B, C))))

attribute [class] LaxMonoidalCategory

namespace LaxMonoidalCategory
  infix `⊗`:70 := λ {Obj : Type} {Hom : Obj → Obj → Type}
                    {C : LaxMonoidalCategory Obj Hom} (A B : Obj),
                    tensor C <$> (A, B)
  infix `⊗m`:70 := λ {Obj : Type} {Hom : Obj → Obj → Type}
                     {C : LaxMonoidalCategory Obj Hom} {A B C D : Obj}
                     (f : Hom A B) (g : Hom C D),
                     tensor C <$>m (f, g)
end LaxMonoidalCategory

open LaxMonoidalCategory

-- This is okay, but surely there's a better way
instance LaxAsCategory {Obj : Type} {Hom : Obj → Obj → Type}
         (C : LaxMonoidalCategory Obj Hom) : Category Obj Hom :=
  ⟨identity C, compose C, left_identity C, right_identity C, associativity C⟩

--theorem LiftForgetLax {Obj : Type} {Hom : Obj → Obj → Type} (C : Category Obj Hom) :
--        Π {tensor : Functor (C ×c C) C} {unit : Obj}
--        {associator : Π (A B C : Obj), Hom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))},
--        LaxAsCategory.mk


def ℕLaxMonoidalCategory : LaxMonoidalCategory unit (λ A B, ℕ) :=
  { ℕCategory with
    tensor     := ℕTensorProduct,
    unit       := (),
    associator := λ A B C, Category.identity ℕCategory ()
  }

