open tactic
open interactive
open lean.parser
open interactive.types expr
open expr interactive.types

local postfix `?`:9001 := optional

meta def propagate_tags (tac : tactic unit) : tactic unit :=
do tag ← get_main_tag,
   if tag = [] then tac
   else focus1 $ do
     tac,
     gs ← get_goals,
     when (bnot gs.empty) $ do
       new_tag ← get_main_tag,
       when new_tag.empty $ with_enable_tags (set_main_tag tag)

meta def simp_core_aux (cfg : simp_config) (discharger : tactic unit) (s : simp_lemmas) (u : list name) (hs : list expr) (tgt : bool) : tactic unit :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← simplify s u h_type cfg `eq discharger,
             assert h.local_pp_name new_h_type,
             mk_eq_mp pr h >>= tactic.exact >> return tt)
         <|>
         (return ff) },
   goal_simplified ← if tgt then (simp_target s u cfg discharger >> return tt) <|> (return ff) else return ff,
   guard (cfg.fail_if_unchanged = ff ∨ to_remove.length > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify",
   to_remove.mmap' (λ h, try (clear h))

meta def simp_core' (cfg : simp_config) (discharger : tactic unit)
                   (no_dflt : bool) (hs : list simp_arg_type) (attr_names : list name)
                   (locat : loc) : tactic unit :=
match locat with
| loc.wildcard := do (all_hyps, s, u) ← mk_simp_set_core no_dflt attr_names hs tt,
                     trace all_hyps,
                     if all_hyps then tactic.simp_all s u cfg discharger
                     else do hyps ← non_dep_prop_hyps, 
                             trace hyps,
                             simp_core_aux cfg discharger s u hyps tt
| _            := do (s, u) ← mk_simp_set no_dflt attr_names hs,
                     ns ← locat.get_locals,
                     simp_core_aux cfg discharger s u ns locat.include_goal
end
>> try tactic.triv >> try (tactic.reflexivity reducible)

namespace tactic.interactive
meta def simp' (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
propagate_tags (simp_core' cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)
end tactic.interactive

lemma foo (p : ite (tt = ff) unit empty) : false :=
begin
simp_all,
simp' at *, -- FIXME this works, but `simp at *` doesn't
induction p
end
