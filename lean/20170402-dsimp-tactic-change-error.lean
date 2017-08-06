structure IsomorphicTypes ( α β : Type ) :=
  ( morphism : α → β )
  ( inverse  : β → α )
  ( witness_1 : morphism ∘ inverse = id )
  ( witness_2 : inverse ∘ morphism = id )

definition test : IsomorphicTypes (((ℕ × ℕ) × ℕ)) (ℕ × (ℕ × ℕ)) :=
begin
    refine {
        morphism := λ t, (t.1.1, (t.1.2, t.2)),
        inverse  := _,
        witness_1 := _,
        witness_2 := _
    },
    intros,
    induction a with a1 a23,
    induction a23 with a2 a3,
    split,
    split,
    all_goals { try { apply funext, intros } },
    all_goals { try { simp } },
    all_goals { try { dsimp } },
    -- apply prod.rec,
    tactic.focus [ `[skip], `[skip], `[skip], `[induction x with x1 x23], `[skip] ],
    tactic.focus [ `[skip], `[skip], `[skip], `[induction x23 with x2 x3], `[skip] ],
    tactic.focus [ `[skip], `[skip], `[skip], `[skip], `[induction x with x12 x3] ],
    tactic.focus [ `[skip], `[skip], `[skip], `[skip], `[induction x12 with x1 x2] ],
    any_goals { dsimp },
    any_goals { simp },
end