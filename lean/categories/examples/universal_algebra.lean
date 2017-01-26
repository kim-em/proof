import data.tuple

structure Operad :=
  (operations : list (nat × nat))
-- relations, too!

structure algebra_over_operad (O: Operad) { α : Type }
--  (operations : ?) -- heterogeneous list of functions between tuples

structure morphism_over_operad (O: Operad) { α β : Type } 
  (map : α → β)
--  (preserving_structure : ?)