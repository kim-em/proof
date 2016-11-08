import standard

structure Category : Type :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  
  (Id : Π A : Obj, Hom A A)
  (compose : Π ⦃A B C : Obj⦄, Hom B C → Hom A B → Hom A C)

  (Id_left  : Π ⦃A B : Obj⦄ (f : Hom A B), compose !Id f = f)
  (Id_right : Π ⦃A B : Obj⦄ (f : Hom A B), compose f !Id = f)
  (assoc : Π ⦃A B C D : Obj⦄ (f : Hom C D) (g : Hom B C) (h : Hom A B),
    compose (compose f g) h = compose f (compose g h))

namespace Category
  -- Can we put this before the definition?
  notation f ∘ g := compose _ _ _ _ f g
  --infixr `∘` := compose _ _ _ _
  infixl `⟶` :25 := Hom _
  --definition Mor := Hom
end Category

open Category
open nat

definition ℕCategory : Category :=
  ⦃ Category,
     Obj     := unit,
     Hom     := λ A B, ℕ,
     Id      := λ A, 0,
     compose := λ A B C, add,

     Id_left  := λ A B, zero_add,
     Id_right := λ A B, add_zero,
     assoc    := λ A B C D, nat.add_assoc ⦄

structure Functor (source target : Category) : Type :=
  (onObj : Obj source → Obj target)
  (onMor : Π ⦃A B : Obj source⦄, Hom source A B → Hom target (onObj A) (onObj B))
  
  (respect_Id   : Π (A : Obj source), onMor (Id source A) = Id target (onObj A))
  (respect_comp : Π ⦃A B C : Obj source⦄ (f : Hom source A B) (g : Hom source B C),
                    onMor (compose source g f)
                     = compose target (onMor g) (onMor f))

definition double : ℕ → ℕ
| double x := x + x

definition distribu : Π (n m : ℕ), (n + m) + (n + m) = (n + n) + (m + m) :=
  sorry

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  ⦃ Functor,
    onObj := id,
    onMor := λ A B, double,

    respect_Id   := λ A, rfl,
    respect_comp := sorry
      --begin
      --  intro A B C f g,
      --  cases f,
      --  cases g,
      --  apply rfl,
      --  apply rfl,
      --  cases g,
      --end
      ⦄

open prod

definition CartesianProduct (C D : Category) : Category :=
  ⦃ Category,
    Obj := Obj C × Obj D,
    Hom := λ A B, Hom C (pr1 A) (pr1 B) × Hom D (pr2 A) (pr2 B),
    --Hom := λ A B, match (A, B) with
    --         ((A₁, A₂), (B₁, B₂)) := Hom C A₁ B₁ × Hom D A₂ B₂
    --         end,

    Id  := λ A, match A with
             (A₁, A₂) := (Id C A₁, Id D A₂)
           end,
    compose := λ A B E f g, (compose A (pr1 f) (pr1 g), compose B (pr2 f) (pr2 g)),
--match f with
                 --(f₁, f₂) := match g with
                   --(g₁, g₂) := (compose A f₁ g₁, compose B f₂ g₂)
                 --end
               --end,

    Id_left  := sorry,
    Id_right := sorry,
    assoc    := sorry ⦄
