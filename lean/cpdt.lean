namespace tactic
open tactic

meta def appHyps (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []      := fail "appHyps failed, no goals work"
   | (g::rs) := tac 

end tactic
