import standard
--import data.nat

class Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  
  (Id : Π A : Obj, Hom A A)
  (compose : Π ⦃A B C : Obj⦄, Hom B C → Hom A B → Hom A C)

  (Id_left  : Π ⦃A B : Obj⦄ (f : Hom A B), compose (Id _) f = f)
  (Id_right : Π ⦃A B : Obj⦄ (f : Hom A B), compose f (Id _) = f)
  (assoc : Π ⦃A B C D : Obj⦄ (f : Hom C D) (g : Hom B C) (h : Hom A B),
    compose (compose f g) h = compose f (compose g h))

namespace Category
  -- Can we put this before the definition?
  notation f `∘` g := compose _ f g
  infix `⟶` :25 := Hom _

  --def Mor := Hom
end Category

open Category 

instance ℕCategory : Category :=
  { Category .
    Obj     := unit,
    Hom     := λ a b, ℕ,
    Id      := λ a, 0,
    compose := λ a b c, add,

    Id_left  := λ a b, zero_add,
    Id_right := λ a b, add_zero,
    assoc    := λ a b c d, add_assoc }

instance ℕCategory' : Category :=
begin
  refine (Category.mk unit (λ a b, ℕ) (λ a, 0) (λ a b c, add) _ _ _),
  intros A B,
  exact zero_add,
  intros A B,
  exact add_zero,
  intros A B C D,
  exact add_assoc
end

--structure Functor {obj : Type} [source : Category obj] :=
-- (onObj : obj) 
-- (onMor : Π {a b : obj}, Hom _ a b → Hom _ a b)
--class Functor (Obj₁ Obj₂ : Type) [source : Category Obj₁] [target : Category Obj₂] :=
--  (onObj : source → target)
  --(onMor : Π ⦃a b : Obj source⦄, Hom _ a b → Hom _ (onObj a) (onObj b))
  --
  --(respect_Id   : Π (a : Obj source), onMor (Id _ a) = Id _ (onObj a))
  --(respect_comp : Π ⦃a b c : Obj source⦄ (f : Hom _ b c) (g : Hom _ a b),
  --                  onMor (f ∘ g) = onMor f ∘ onMor g)

--namespace Functor
--  infix `<$>`:50 := λ {C D : Category} (F : Functor C D) (a : Obj C), onObj F a
--  infix `<$>m`:50 := λ {C D : Category} (F : Functor C D) {a b : Obj C}
--                        (f : Hom _ a b), onMor F f
--end Functor
--
--open function
--
--theorem double_order (n m p q : ℕ) : n + m + (p + q) = n + p + (m + q) :=
--calc
--  n + m + (p + q) = n + (m + (p + q)) : add_assoc n m (p + q)
--              ... = n + (m + p + q)   : eq.symm (congr_arg (add n) (add_assoc m p q))
--              ... = n + (p + m + q)   : congr_arg (add n) (congr_arg (λ n, n + q) (add_comm m p))
--              ... = n + (p + (m + q)) : congr_arg (add n) (add_assoc p m q)
--              ... = n + p + (m + q)   : eq.symm (add_assoc n p (m + q))
--
--@[reducible]
--def DoublingAsFunctor : Functor ℕCategory ℕCategory :=
--  { Functor .
--    onObj := id,
--    onMor := λ a b (n : ℕ), n + n,
--
--    respect_Id   := λ a, rfl,
--    respect_comp := begin
--                    intros,
--                    exact double_order f g f g
--                    end }
--
--open prod
--
--theorem pair_eq {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
--assume H1 H2, H1 ▸ H2 ▸ rfl
--
open prod

theorem pair_eq {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
assume H1 H2, H1 ▸ H2 ▸ rfl

instance ProductCategory (C D : Category) [Category] [Category] : Category :=
  { Category .
    Obj := Obj C × Obj D,
    Hom := λ a b, Hom C (fst a) (fst b) × Hom D (snd a) (snd b),
    Id  := λ a, (Id C (fst a), Id D (snd a)),
    compose := λ a b c f g, (fst f ∘ fst g, snd f ∘ snd g),

    Id_left  := λ a b c d, pair_eq (Id_left C _) (Id_left D _) ,
    Id_right := λ a b c d, pair_eq (Id_right C _) (Id_right D _),
    assoc    := begin
                intros,
                --exact pair_eq (assoc C _ _ _ _ _) (assoc D _ _ _ _ _)
                end }
--
--namespace ProductCategory
--  notation C `×c` D := ProductCategory C D
--end ProductCategory
--
--open Functor
--open ProductCategory
--
--structure LaxMonoidalCategory :=
--  (carrier : Category)
--  (tensor : Functor (carrier ×c carrier) carrier)
--  (unit : let obj := Obj carrier in obj)
--
--  (associator : Π (a b c : Obj carrier),
--                  Hom _ (tensor <$> (tensor <$> (a,b), c))
--                       (tensor <$> (a, tensor <$> (b,c))))
--  --(pentagon : Π (a b c d : Obj carrier),
--  --              associator (tensor <$> (a,b)) c d ∘c associator a b (tensor <$> (c,d)) = 
--
----attribute [coercion] LaxMonoidalCategory.carrier
----
--namespace LaxMonoidalCategory
--  infix `⊗`:70 := λ {C : LaxMonoidalCategory} (a b : Obj C), tensor C <$> (a,b)
--  infix `⊗m`:70 := λ {C : LaxMonoidalCategory} {a b c d : Obj C}
--                      (f : Hom a b) (g : Hom c d), tensor C <$> (f,g)
--end LaxMonoidalCategory

--@[reducible]
--def ℕTensorProduct : Functor (ℕCategory ×c ℕCategory) ℕCategory :=
--  { Functor .
--    onObj := fst,
--    onMor := λ a b n, fst n + snd n,
--
--    respect_Id   := λ a, rfl,
--    respect_comp := begin
--                    intros,
--                    refine (double_order f g f g)
--                    end }

--def ℕTensorProduct' : Functor (ℕCategory ×c ℕCategory) ℕCategory :=
--  Functor.mk pr1 (λ a b (f : ℕ × ℕ), pr1 f + pr2 f) _ _ _
--begin
--  refine Functor.mk (pr1) (λ (a b : unit), λ (f : ℕ × ℕ), pr1 f + pr2 f) _ _,
--end
--
--def ℕLaxMonoidalCategory : LaxMonoidalCategory :=
--  ⦃ LaxMonoidalCategory,
--    carrier    := ℕCategory,
--    tensor     := ℕTensorProduct,
--    unit       := unit.star,
--
--    associator := λ a b c, Id _ _ ⦄
--
--open LaxMonoidalCategory

--check (2 : Hom ℕLaxMonoidalCategory unit.star unit.star)
