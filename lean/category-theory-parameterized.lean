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

-- (Scott:) I wish it were possible to define coercions of Functor to either
-- onObjects or onMorphisms, so we could just write F A and F f.
-- (Scott:) I'm not sure what purpose these notations serve: is 'F <$> A' that 
-- much better than 'onObjects F A' that it warrants introducing notation?
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

-- TODO(?) Can these proofs be simplified?
-- Stephen's earlier versions (for Lean 2?) were perhaps better.
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
/- I tried writing the pentagon, but it doesn't type check. :-(
  (pentagon : Π (A B C D : Obj),
     -- we need to compare:
     -- ((AB)C)D ---> (A(BC))D ---> A((BC)D) ---> A(B(CD))
     -- ((AB)C)D ---> (AB)(CD) ---> A(B(CD))
     compose
       (compose 
         (tensor <$>m (associator A B C, identity D))
         (associator A (tensor <$> (B, C)) D)
       ) (tensor <$>m (identity A, associator B C D)) =
     compose
       (associator (tensor <$> (A, B)) C D)
       (associator A B (tensor <$> (C, D)))

  )
-/

-- Notice that LaxMonoidalCategory.tensor has a horrible signature...
-- It sure would be nice if it read ... Functor (carrier ×c carrier) carrier
print LaxMonoidalCategory

attribute [class] LaxMonoidalCategory
attribute [instance] LaxMonoidalCategory.to_Category

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

-- casting is not working: we really want to be able to write the following:
/-
instance DoublingAsFunctor' : Functor ℕLaxMonoidalCategory ℕLaxMonoidalCategory :=
  { onObjects   := id,
    onMorphisms := (λ A B n, n + n),
    identities    := by blast,
    functoriality := by blast
  }
-/
