meta def rwonce : tactic unit :=
do r ← tactic.to_expr `(FunctorComposition.associativity),
   a ← tactic.to_expr `(associator),
   tactic.rewrite_at_core reducible tt tt (occurrences.pos [2]) tt r a

meta def rwonce_2 : tactic unit :=
do r ← tactic.to_expr `(switch_twice_is_the_identity),
   a ← tactic.to_expr `(switch_twice),
   tactic.rewrite_at_core reducible tt tt (occurrences.pos [1]) tt r a

meta def rwonce_3 : tactic unit :=
do r ← tactic.to_expr `(FunctorComposition.left_identity),
   a ← tactic.to_expr `(identitor),
   tactic.rewrite_at_core reducible tt tt (occurrences.pos [2]) ff r a

