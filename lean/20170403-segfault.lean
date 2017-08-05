open list tactic monad expr

meta def induction_on_pairs : tactic unit :=
repeat ( do l ← local_context,
   l.reverse.mfor' $ λ h, do
     ```(prod _ _) ← infer_type h >>= whnf | skip,
     induction h [ const_name h ] >> skip )

lemma f ( p : ℕ × ℕ ) : ℕ :=
begin
  induction_on_pairs
end