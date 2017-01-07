import standard

meta def blast : tactic unit :=
using_smt $ return ()

structure Category (Obj : Type) (Hom : Obj -> Obj -> Type) :=
  (identity : Π A : Obj, Hom A A)
  (compose  : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)

attribute [class] Category

open Category

structure MonoidalCategory (Obj : Type) (Hom : Obj → Obj → Type)
  extends carrier : Category Obj Hom :=
  (unit : Obj)

variables { Obj₁ Obj₂ : Type }
variables { Hom₁ : Obj₁ → Obj₁ → Type } { Hom₂ : Obj₂ → Obj₂ → Type }

structure Functor (C₁ : Category Obj₁ Hom₁) (C₂ : Category Obj₂ Hom₂) :=
  (onObjects   : Obj₁ → Obj₂)
  (onMorphisms : Π ⦃A B : Obj₁⦄,
                Hom₁ A B → Hom₂ (onObjects A) (onObjects B))
  (identities : Π (A : Obj₁),
    onMorphisms (identity C₁ A) = identity C₂ (onObjects A))

definition ℕCategory : Category unit (λ a b, ℕ) :=
  { identity := λ a, 0,
    compose  := λ a b c, add
  }

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ A B n, n + n),
    identities    := by blast
  }

attribute [instance] MonoidalCategory.to_Category

definition ℕMonoidalCategory : MonoidalCategory unit (λ A B, ℕ) :=
  { ℕCategory with
    unit       := ()
  }

-- casting is not working: we really want to be able to write the following:
definition DoublingAsFunctor' : Functor ℕMonoidalCategory ℕMonoidalCategory :=
  { onObjects   := id,
    onMorphisms := (λ A B n, n + n),
    identities    := by blast
  }
