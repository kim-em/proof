open tactic

meta def simp_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   guard (new_htype \ne )
   assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   clear h