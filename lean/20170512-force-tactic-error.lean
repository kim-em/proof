open tactic

meta def force { α : Type } (t : tactic α) : tactic α :=
  do gs ← get_goals,
     a ← t,
     gs' ← get_goals,
     guard (gs ≠ gs') <|> fail "force tactic failed",
     return a

namespace tactic.interactive
  meta def force (t : itactic) : tactic unit := _root_.force t
end tactic.interactive

set_option pp.all true

lemma a ( p q : nat ) : 1 = 1 :=
begin
  -- p q : nat
  -- ⊢ @eq.{1} nat (@one.{0} nat nat.has_one) (@one.{0} nat nat.has_one)
  force {
    revert q,
    intron 1
    -- p q : nat
    -- ⊢ @eq.{1} nat (@one.{0} nat nat.has_one) (@one.{0} nat nat.has_one)
  } -- ... but force succeeds here.
end