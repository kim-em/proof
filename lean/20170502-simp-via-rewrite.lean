open tactic

-- Applies a list of tactics in turn, always succeeding.
meta def list_try_seq : list (tactic unit) → tactic unit 
| list.nil  := skip
| (t :: ts) := seq (try t) (list_try_seq ts)

-- Applies a list of tactics in turn, succeeding if at least one succeeds.
meta def at_least_one : list (tactic unit) → tactic unit
| list.nil  := fail "at_least_one tactic failed, no more tactics"
| (t :: ts) := (seq t (list_try_seq ts)) <|> (at_least_one ts)

-- FIXME let's try this
meta def simp_at_via_rewrite (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   rewrite_at_core reducible tt tt occurrences.all ff heq h

-- set_option pp.all true

lemma {u v} dependent_pair_equality {α : Type u} {Z : α → Type v} { X Y : Σ a : α, Z a } ( p1 : X.1 = Y.1 ) ( p2 : @eq.rec α X.1 Z X.2 Y.1 p1 = Y.2 ) : X = Y :=
begin
  induction X,
  induction Y,
  dsimp at p1,
  dsimp at p2,
  
end

-- FIXME this repeatedly resimplifies hypotheses, if they can't be cleared. :-(
meta def simp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, simp_at h))