import standard
import data.nat

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
  notation f `∘` g := compose _ f g
  infix `⟶` :25 := Hom _

  definition Mor := Hom

  -- Do these do anything?
  attribute mk [constructor]
  attribute Obj [unfold 1]
  attribute Hom [unfold 1]
  attribute Id [unfold 1]
  attribute compose [unfold 1]
end Category

open Category 
open nat

definition ℕCategory : Category :=
  ⦃ Category,
    Obj     := unit,
    Hom     := λ a b, ℕ,
    Id      := λ a, 0,
    compose := λ a b c, add,

    Id_left  := by blast,
    Id_right := by blast,
    assoc    := by blast ⦄

--definition ℕCategory' : Category :=
--begin
--  refine (Category.mk unit (λ a b, ℕ) (λ a, 0) (λ a b c, add) _ _ _),
--end

structure Functor (source target : Category) : Type :=
  (onObj : Obj source → Obj target)
  (onMor : Π ⦃a b : Obj source⦄, !Hom a b → !Hom (onObj a) (onObj b))
  
  (respect_Id   : Π (a : Obj source), onMor (Id _ a) = Id _ (onObj a))
  (respect_comp : Π ⦃a b c : Obj source⦄ (f : !Hom b c) (g : !Hom a b),
                    onMor (f ∘ g) = onMor f ∘ onMor g)

namespace Functor
  infix `<$>`:50  := λ {C D : Category} (F : Functor C D) (a : Obj C), onObj F a
  infix `<$>m`:50 := λ {C D : Category} (F : Functor C D) {a b : Obj C}
                       (f : !Hom a b), onMor F f
end Functor

theorem double_order (n m p q : ℕ) : n + m + (p + q) = n + p + (m + q) :=
  by blast
--calc
--  n + m + (p + q) = n + (m + (p + q)) : add.assoc n m (p + q)
--              ... = n + (m + p + q)   : congr_arg (add n) (add.assoc m p q)
--              ... = n + (p + m + q)   : congr_arg (add n) (congr_arg (swap add q) (add.comm m p))
--              ... = n + (p + (m + q)) : congr_arg (add n) (add.assoc p m q)
--              ... = n + p + (m + q)   : add.assoc n p (m + q)

definition DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  ⦃ Functor,
    onObj := id,
    onMor := λ a b (x : ℕ), x + x,

    respect_Id   := by intros; trivial,
    respect_comp := λ a b c f g, double_order f g f g⦄
    --respect_comp := begin
    --                intros,
    --                unfold [ℕCategory],
    --                exact (double_order f g f g)
    --                end ⦄

open prod

definition ProductCategory (C D : Category) : Category :=
  ⦃ Category,
    Obj := Obj C × Obj D,
    Hom := λ a b, Hom C (pr1 a) (pr1 b) × Hom D (pr2 a) (pr2 b),
    Id  := λ a, (Id C (pr1 a), Id D (pr2 a)),
    compose := λ a b c f g, (pr1 f ∘ pr1 g, pr2 f ∘ pr2 g),

    Id_left  := by intros; exact prod.eq !Id_left !Id_left,
    Id_right := by intros; exact prod.eq !Id_right !Id_right,
    assoc    := by intros; exact prod.eq !assoc !assoc ⦄

namespace ProductCategory
  notation C `×c` D := ProductCategory C D
end ProductCategory

open Functor
open ProductCategory

structure LaxMonoidalCategory extends cat : Category :=
  (tensor : Functor (cat ×c cat) cat)
  (unit : Obj)
  
  (associator : Π (a b c : Obj)
                  (infix `⊗`:70 := λ (a b : Obj), tensor <$> (a, b)),
                    Hom ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c)))
  (pentagon : Π (a b c d : Obj)
                (infix `∘`     := compose)
                (infix `⊗`:70  := λ (x y : Obj), tensor <$> (x, y))
                (infix `⊗m`:70 := λ {x y z w : Obj} (f : Hom x y) (g : Hom z w),
                  tensor <$>m (f, g)),
                let α := associator in
                  (Id a ⊗m α b c d) ∘ (α a (b ⊗ c) d) ∘ (α a b c ⊗m Id d)
                    = α a b (c ⊗ d) ∘ α (a ⊗ b) c d)
   
  (unitor_left  : Π (a : Obj)
                    (infix `⊗`:70 := λ (a b : Obj), tensor <$> (a, b)),
                      Hom (unit ⊗ a) a)
  (unitor_right : Π (a : Obj)
                    (infix `⊗`:70 := λ (a b : Obj), tensor <$> (a, b)),
                      Hom (a ⊗ unit) a)
  (triangle : Π (a b : Obj)
                (infix `∘`     := compose)
                (infix `⊗`:70  := λ (x y : Obj), tensor <$> (x, y))
                (infix `⊗m`:70 := λ {x y z w : Obj} (f : Hom x y) (g : Hom z w),
                  tensor <$>m (f, g)),
                let L := unitor_left, R := unitor_right, α := associator in
                  R a ⊗m Id b = (Id a ⊗m L b) ∘ α a unit b)

namespace LaxMonoidalCategory
  infix `⊗`:70  := λ {C : LaxMonoidalCategory} (a b : Obj C), tensor C <$> (a,b)
  infix `⊗m`:70 := λ {C : LaxMonoidalCategory} {a b c d : Obj C}
                     (f : Hom a b) (g : Hom c d), tensor C <$> (f,g)
end LaxMonoidalCategory

definition ℕTensorProduct : Functor (ℕCategory ×c ℕCategory) ℕCategory :=
  ⦃ Functor,
    onObj := pr1,
    onMor := λ a b (f : ℕ × ℕ), pr1 f + pr2 f,

    respect_Id   := by intros; trivial,
    respect_comp := λ a b c (f g : ℕ × ℕ), by krewrite double_order ⦄

--definition ℕTensorProduct' : Functor (ℕCategory ×c ℕCategory) ℕCategory :=
--  Functor.mk pr1 (λ a b (f : ℕ × ℕ), pr1 f + pr2 f) _ _ _
--begin
--  refine Functor.mk (pr1) (λ (a b : unit), λ (f : ℕ × ℕ), pr1 f + pr2 f) _ _,
--end

definition ℕLaxMonoidalCategory : LaxMonoidalCategory :=
  ⦃ LaxMonoidalCategory,
    ℕCategory,
    tensor := ℕTensorProduct,
    unit   := unit.star,

    associator := λ a b c, Id _ _,
    pentagon := sorry,

    unitor_left  := Id _,
    unitor_right := Id _,
    triangle := sorry
    ⦄

open LaxMonoidalCategory

--check (2 : Hom ℕLaxMonoidalCategory unit.star unit.star)
