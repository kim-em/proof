structure X :=
  ( x : nat )

definition S ( a : X ) : X := { x := a.x }

definition f ( a : X ) ( n : nat ) : nat := 1

lemma foo ( a : X ) : f (S a) (S a).x = 0 :=
begin
  -- I want a tactic that will unfold `(S a).x` to `a.x`, but leave the other `(S a)` entirely alone.

-- Use transitivity for first simplification
  transitivity,
  { -- Select subterm
    apply congr_arg (f (S a)),
    -- Unfold S
    unfold S,
    -- Resolve meta variable
    refl,
  },
  dsimp,
  -- admit, 
end