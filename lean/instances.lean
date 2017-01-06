structure foo :=
  (x: unit)

definition bar : foo := { x := unit.star }

attribute [class] unit
instance star : unit := unit.star

definition baz : foo := { x := _ }
