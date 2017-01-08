structure C1 := (a: unit)
structure C2 extends C1

attribute [class] C1 C2
instance : has_coe C2 C1 := ⟨C2.to_C1⟩
instance C2_to_C1 [ c2: C2 ] : C1 := c2

definition X1: C1 := { a := unit.star }
definition X2: C2 := { a := unit.star }

definition f (c: C1) := ()

definition works_fine  := f X1
definition doesnt_work := f X2

instance X : C2 := X2
definition Y: C1 := by apply_instance

