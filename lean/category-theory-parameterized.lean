import standard

meta def blast : tactic unit :=
using_smt $ return ()

variable Obj : Type
variable Hom : Obj -> Obj -> Type
-- I'm not sure how to use these in Category, as it keeps assigning
-- them as arguments to Category itself.
variables (A B C D : Obj) (f : Hom A B) (g : Hom B C) (h : Hom C D)

class Category :=
  (identity : Π A : Obj, Hom A A)
  (compose  : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)
  
  (left_identity  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (identity _) f = f)
  (right_identity : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (identity _) = f)
  (associativity  : Π ⦃A B C D : Obj⦄ (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h))

end foo

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

variables { Obj_1 Obj_2 : Type }
variables { Hom_1 : Obj_1 → Obj_1 → Type } { Hom_2 : Obj_2 → Obj_2 → Type }

class Functor (C₁ : Category Obj_1 Hom_1) (C₂ : Category Obj_2 Hom_2) :=
  (onObjects   : Obj_1 → Obj_2)
  (onMorphisms : Π ⦃A B : Obj_1⦄,
                Hom_1 A B → Hom_2 (onObjects A) (onObjects B))
  (identities : Π (A : Obj_1),
    onMorphisms (identity _ A) = identity _ (onObjects A))
  (functoriality : Π ⦃A B C : Obj_1⦄ (f : Hom_1 A B) (g : Hom_1 B C),
    onMorphisms (compose _ f g) = compose _ (onMorphisms f) (onMorphisms g))

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
