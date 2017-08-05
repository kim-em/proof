open tactic
open lean.parser
open interactive




namespace tactic.interactive


open lean
open lean.parser

private meta def resolve_name' (n : name) : tactic expr :=
do {
  p ← resolve_name n,
  match p.to_raw_expr with
  | expr.const n _           := mk_const n -- create metavars for universe levels
  | _                        := i_to_expr p
  end
}

private meta def to_expr' (p : pexpr) : tactic expr :=
let e := p.to_raw_expr in
match e with
| (expr.const c [])          := do new_e ← resolve_name' c, save_type_info new_e e, return new_e
| (expr.local_const c _ _ _) := do new_e ← resolve_name' c, save_type_info new_e e, return new_e
| _                     := i_to_expr p
end

private meta def rw_goal_gos (m : transparency) (r : rw_rule) : tactic unit :=
save_info r.pos >> to_expr' r.rule >>= rewrite_core m tt tt occurrences.all r.symm



  meta def rewrite_nth (r : parse ident) (n : nat) : tactic unit :=
  do e ← tactic.mk_const r,
    tactic.rewrite_core reducible tt tt (occurrences.pos [n]) tt r
end tactic.interactive

lemma foo (p : 1 = 2): [ 1,1,1,2,1 ] = [ 1,1,2,2,1 ] :=
begin
induction p,
  rewrite_nth p 3,
end