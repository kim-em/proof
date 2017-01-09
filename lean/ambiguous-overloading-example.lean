import standard

structure Category :=
  (Obj : Type)

open Category

structure LaxMonoidalCategory
  extends carrier : Category

instance LaxMonoidalCategory_coercion_to_Category : has_coe LaxMonoidalCategory Category := 
  ⟨LaxMonoidalCategory.to_Category⟩

open LaxMonoidalCategory

structure MonoidalCategory
  extends LaxMonoidalCategory

instance MonoidalCategory_coercion_to_LaxMonoidalCategory : has_coe MonoidalCategory LaxMonoidalCategory := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩

definition tensor_on_left (C: MonoidalCategory) (X: Obj C) : unit := unit.star
