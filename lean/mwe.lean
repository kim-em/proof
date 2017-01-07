class bar :=
  (b: unit)

structure turkle (S: bar) :=
  (t : unit)

class baz extends bar 

definition X: bar := { b := unit.star }
definition Y: baz := { b := unit.star }

definition works_fine  := turkle.mk X unit.star
definition doesnt_work := turkle.mk Y unit.star
