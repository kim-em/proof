structure C :=
  (Obj : Type)

structure D
  extends C

instance D_coercion_to_C: has_coe D C := 
  ⟨D.to_C⟩

structure E
  extends D

instance E_coercion_to_D : has_coe E D := ⟨E.to_D⟩

--open C
--open D
--open E

definition F (x: E) (X: x^.Obj) : unit := unit.star
