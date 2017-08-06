

private meta def if_then_else { α β : Type } ( i : tactic unit ) ( t : tactic β ) ( e : tactic β ) : tactic β :=
do r ← tactic.try_core i,
   match r with
   | some _ := t
   | none   := e
   end
private meta def if_dthen_else { α β : Type } ( i : tactic α ) ( t : α → tactic β ) ( e : tactic β ) : tactic β :=
do r ← tactic.try_core i,
   match r with
   | some a := t a
   | none   := e
   end

open tactic
meta def foo : tactic unit := if_dthen_else dsimp (λ x, dsimp) dsimp

-- def mcond {m : Type → Type} [monad m] {α : Type} (mbool : m bool) (tm fm : m α) : m α :=
-- do b ← mbool, cond b tm fm
