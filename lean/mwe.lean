class C1 :=
  (a: unit)
class C2 extends C1

definition X1: C1 := { a := unit.star }
definition X2: C2 := { a := unit.star }

definition f (c: C1) := ()

definition works_fine  := f X1
definition doesnt_work := f X2

instance X : C2 := X2
definition Y: C1 := by apply_instance

