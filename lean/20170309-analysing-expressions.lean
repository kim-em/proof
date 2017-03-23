open tactic
open tactic.interactive

meta def occuring_in ( targets : list expr ) ( e : expr ) : list expr := list.filter (λ t, expr.occurs t e) targets

meta def fail_if_empty { α : Type } (or_else : list expr → tactic α) : list expr → tactic α
| list.nil := failed
| l := or_else l

meta def unfold_at_least_one ( targets : list expr ) : tactic unit :=
  monad.map (occuring_in targets) target >>= (fail_if_empty dsimp)

meta def unfold_at_least_one_with_attribute ( attr : name ) : tactic unit :=
  attribute.get_instances attr >>= unfold_at_least_one