import standard


structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  
  (identity : Π A : Obj, Hom A A)
  (compose : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)

  (left_identity  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (identity A) f = f)
  (right_identity : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (identity B) = f)
  (associativity  : Π ⦃A B C D : Obj⦄ (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h))

namespace Category
  -- Can we put this before the definition?
  notation f ∘ g := compose _ _ _ _ f g
  -- infixr `∘` := compose _ _ _ _
  infixl `⟶` :25 := Hom _
  variables C : Category
  variables {a b c d : Obj C} 
end Category

open Category

definition ℕCategory : Category :=
  { Category .
     Obj      := unit,
     Hom      := λ A B, ℕ,
     identity := λ A, 0,
     compose  := λ A B C, add, 

     left_identity  := begin
                         intros
                         generalize f,
                         exact zero_add
                       end,
     right_identity := λ A B, add_zero,
     associativity    := λ A B C D, add_assoc }

structure Functor (source target : Category) :=
  (onObjects     : Obj source → Obj target)
  (onMorphisms   : Π ⦃A B : Obj source⦄, Hom source A B → Hom target (onObjects A) (onObjects B))
  
  (identities    : Π (A : Obj source), onMorphisms (identity source A) = identity target (onObjects A))
  (functoriality : Π ⦃A B C : Obj source⦄ (f : Hom source A B) (g : Hom source B C),
                    onMorphisms (compose source f g)
                     = compose target (onMorphisms f) (onMorphisms g))

definition double(x : ℕ) := x + x

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { 
    onObjects := id,
    onMorphisms := λ A B, double,

    identities   := begin
                      intro A,
                      induction A,
                      exact sorry
                    end,
    functoriality := 
      begin
       intros A B C f g,
       induction A,
       induction B,
       induction C,
       cases f,
       cases g,
       apply rfl,
      -- apply rfl,
      --  cases g,
       exact sorry,
       exact sorry
      end
  }

open prod

definition CartesianProduct (C D : Category) : Category :=
  { Category .
    Obj := Obj C × Obj D,
    Hom := λ A B, Hom C (fst A) (fst B) × Hom D (snd A) (snd B),
    --Hom := λ A B, match (A, B) with
    --         ((A₁, A₂), (B₁, B₂)) := Hom C A₁ B₁ × Hom D A₂ B₂
    --         end,

    identity  :=
           λ A, match A with
             (A₁, A₂) := (identity C A₁, identity D A₂)
           end,
    compose := λ A B E f g, (compose A (fst f) (fst g), compose B (snd f) (snd g)),
--match f with
                 --(f₁, f₂) := match g with
                   --(g₁, g₂) := (compose A f₁ g₁, compose B f₂ g₂)
                 --end
               --end,

    left_identity    := sorry,
    right_identity   := sorry,
    associativity    := sorry ⦄
