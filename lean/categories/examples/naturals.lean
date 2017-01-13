-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..functor
import ..natural_transformation
import ..products
import ..monoidal_category

namespace tqft.categories.examples.naturals

instance ℕCategory : Category :=
  {
    Obj := unit,
    Hom := λ _ _, ℕ,
    identity := λ _, 0,
    compose  := λ _ _ _, add,

    left_identity  := λ _ _, zero_add,
      -- Sadly, "by blast" doesn't work here. I think this is because
      -- "by blast" checks if the heads of the expressions match,
      -- which is the case for right_identity and associativity, but
      -- not left_identity.
    right_identity := by blast, --λ a b, add_zero,
    associativity  := by blast  --λ a b c d, add_assoc
  }    

instance DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ _ _ n, n + n),
      /-
      -- Sadly, "by blast" doesn't work below if we replace "n + n"
      -- with "2 * n".  Again, I think this is because the heads don't
      -- match. If you use "n * 2", then identities works by blast,
      -- but functoriality still doesn't.
      -/
    identities    := by blast,
    functoriality := by blast
  }

def ℕTensorProduct : Functor (ℕCategory × ℕCategory) ℕCategory :=
  { onObjects     := prod.fst,
    onMorphisms   := λ _ _ n, n^.fst + n^.snd,
    identities    := by blast,
    functoriality := by blast
  }

def ℕLaxMonoidalCategory : LaxMonoidalCategory :=
  { ℕCategory with
    tensor       := ℕTensorProduct,
    tensor_unit  := (),
    associator   := λ _ _ _, Category.identity ℕCategory (),
    interchange  := begin
                      exact sorry -- should be trivial, but how?
                    end
  }

end tqft.categories.examples.naturals