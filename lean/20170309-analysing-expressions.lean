open tactic

structure C := 
  ( xxx : Type )

meta def occuring_in ( targets : list expr ) ( e : expr ) : list expr := list.filter (λ t, expr.occurs t e) targets

meta def fail_if_empty { α : Type } (or_else : list expr → tactic α) : list expr → tactic α
| list.nil := failed
| l := or_else l

meta def unfold_at_least_one ( targets : list expr ) : tactic unit :=
  monad.map (occuring_in targets) target >>= unfold

meta def analyse : tactic unit :=
  target >>= contains_xxx >>= trace

def c : C := { xxx := unit }

lemma A : 0 = 1 := by analyse
lemma B : c^.xxx = ℕ := by analyse
