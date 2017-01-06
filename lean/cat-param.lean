import standard

-- Oh, there it is.
meta def blast : tactic unit :=
using_smt $ return ()

class Category (Obj : Type) (Hom : Obj → Obj → Type) :=
  (identity : Π A : Obj, Hom A A)
  (compose  : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)
  
  (left_identity  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (identity _) f = f)
  (right_identity : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (identity _) = f)
  (associativity  : Π ⦃A B C D : Obj⦄ (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h))

instance ℕCategory : Category unit (λ a b, ℕ) :=
  { identity := λ a, 0,
    compose  := λ a b c, add,

    left_identity  := λ a b, zero_add, -- sadly, "by blast" doesn't work here
    right_identity := by blast, --λ a b, add_zero,
    associativity  := by blast --λ a b c d, add_assoc
  }

open Category

class Functor { Obj₁ : Type } { Hom₁ : Obj₁ → Obj₁ → Type } (C₁ : Category Obj₁ Hom₁)
              { Obj₂ : Type } { Hom₂ : Obj₂ → Obj₂ → Type } (C₂ : Category Obj₂ Hom₂) :=
  (onObjects   : Obj₁ → Obj₂)
  (onMorphisms : Π ⦃A B : Obj₁⦄,
                Hom₁ A B → Hom₂ (onObjects A) (onObjects B))
  (identities : Π (A : Obj₁),
    onMorphisms (identity _ A) = identity _ (onObjects A))
  (functoriality : Π ⦃A B C : Obj₁⦄ (f : Hom₁ A B) (g : Hom₁ B C),
    onMorphisms (compose _ f g) = compose _ (onMorphisms f) (onMorphisms g))
  
instance DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { 
    onObjects     := id,
    onMorphisms   := (λ A B n, n + n), -- sadly, "by blast" doesn't work below if we replace "n + n" with "2 * n"
    identities    := by blast,
    functoriality := by blast
  }
