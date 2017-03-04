open tactic

notation `♮` := by abstract { begin intros, simp end }

structure Monoid ( α : Type ) :=
  (one : α)
  (multiply  : α → α → α)
  (left_identity  : ∀ ( f : α ), multiply one f = f)
  (right_identity : ∀ ( f : α ), multiply f one = f)
  (associativity  : ∀ ( f g h : α ),
    multiply (multiply f g) h = multiply f (multiply g h))

meta def try_with (n : nat) : tactic unit :=
   -- (quote n) converts the natural number n into a pre-expression
   -- We can also use `[exact %%(quote n)]
do to_expr (quote n) >>= exact, 
   -- Solve all remaining goals using `intros` followed by `simp`
   all_goals (intros >> simp),
   -- `now` will fail if there are unsolved goals
   now 

meta def guess_upto : nat → nat → tactic unit
| k n :=
  -- Try to solve using k
  try_with k
  <|> 
  -- If try_with k failed, then we fail if k = n, otherwise we continue with k+1
  if k = n then failed
  else guess_upto (k+1) n

-- The default value for max is 100. So, we will only search up to 100.
meta def guess (max := 100) : tactic unit :=
guess_upto 0 max

definition NaturalsAsAddMonoid : Monoid ℕ :=
begin
  refine { multiply       := λ a b, a + b,
           one            := _,
           left_identity  := _,
           right_identity := _,
           associativity  := ♮ },
  guess
end

definition NaturalsAsMultMonoid : Monoid ℕ :=
begin
  refine { multiply       := λ a b, a * b,
           one            := _,
           left_identity  := _,
           right_identity := _,
           associativity  := ♮ },
  guess
end