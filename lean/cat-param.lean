/- This is the parameterised implementation of Category. It has the
   disadvantage that we're carrying around a mess of ugly
   parameters. This could be mitigated by defining some convenience
   structures. This is the approach taken in the Lean 2 standard
   library, except with only the objects as a parameter. -/

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

    left_identity  := λ a b, zero_add,
    right_identity := λ a b, add_zero,
    associativity  := λ a b c d, add_assoc
  }

open Category

class Functor (Obj₁ : Type) (Hom₁ : Obj₁ → Obj₁ → Type) [C₁ : Category Obj₁ Hom₁]
              (Obj₂ : Type) (Hom₂ : Obj₂ → Obj₂ → Type) [C₂ : Category Obj₂ Hom₂]
              (onObjects   : Obj₁ → Obj₂)
              (onMorphisms : Π ⦃A B : Obj₁⦄,
                Hom₁ A B → Hom₂ (onObjects A) (onObjects B)) :=
  (identities : Π (A : Obj₁),
    onMorphisms (identity _ A) = identity _ (onObjects A))
  (functoriality : Π ⦃A B C : Obj₁⦄ (f : Hom₁ A B) (g : Hom₁ B C),
    onMorphisms (compose _ f g) = compose _ (onMorphisms f) (onMorphisms g))
  
instance DoublingAsFunctor : Functor unit (λ A B, ℕ) unit (λ A B, ℕ)
                               id (λ A B n, n + n) :=
  { identities    := by blast,
    functoriality := by blast
  }
