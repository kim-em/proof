import standard

meta def blast : tactic unit :=
using_smt $ return ()

variables (Obj Obj' : Type)
variables (Hom : Obj → Obj → Type) (Hom' : Obj' → Obj' → Type)

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

class Functor (C₁ : Category Obj Hom) (C₂ : Category Obj' Hom') :=
  (onObjects   : Obj → Obj')
  (onMorphisms : Π ⦃A B : Obj⦄,
                Hom A B → Hom' (onObjects A) (onObjects B))
  (identities : Π (A : Obj),
    onMorphisms (identity _ A) = identity _ (onObjects A))
  (functoriality : Π ⦃A B C : Obj⦄ (f : Hom A B) (g : Hom B C),
    onMorphisms (compose _ f g) = compose _ (onMorphisms f) (onMorphisms g))
  
-- Can't we get rid of these underscores? I'm not sure this is a good
-- payoff for saving the parameters in the Functor definition.
instance DoublingAsFunctor : Functor _ _ _ _ ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ A B n, n + n),
      -- Sadly, "by blast" doesn't work below if we replace "n + n"
      -- with "2 * n".  Again, I think this is because the heads don't
      -- match. If you use "n * 2", then identities works by blast,
      -- but functoriality still doesn't.
    identities    := by blast,
    functoriality := by blast
  }
