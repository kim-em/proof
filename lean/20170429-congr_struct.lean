namespace tactic
  open expr

  /-- Given a fully applied structure type `ty` with fields `f1`...`fn`, synthesize the proof
      `∀ x : ty, ty.mk x.f1 ... x.fn = x`.
      The proof can be extracted into a new definition using

      ```
      def ty.eta := by mk_struct_eta ```(ty) >>= exact
      ``` -/
  meta def mk_struct_eta (ty : expr) : tactic expr :=
  do (const n ls) ← pure ty.get_app_fn | fail "not a structure",
     env ← get_env,
     fields ← env.structure_fields n <|> fail "not a structre",
     [ctor] ← pure $ env.constructors_of n,
     let proof_ty := pi `_x binder_info.default ty $ app (const ``eq [])
       (expr.mk_app (const ctor []) $ fields.map $ λ f, (pexpr.mk_field_macro (pexpr.of_raw_expr $ var 0) f).to_raw_expr)
       (var 0),
     proof_ty ← to_expr (pexpr.of_raw_expr proof_ty),
     prod.snd <$> solve_aux proof_ty (do x ← intro `_, cases x, reflexivity)
end tactic

namespace tactic.interactive
  open expr tactic

  private meta def common_app_prefix : expr → expr → tactic expr
  | (app e₁ e₁') (app e₂ e₂') := (is_def_eq e₁ e₂ *> pure e₁) <|> common_app_prefix e₁ e₂
  | e₁           e₂           := fail "no common head symbol"

  /-- Given a goal of form `f a₁ ... aₙ == f a₁' ... aₙ'`, this tactic breaks it down to subgoals
      `a₁ == a₁'`, ...
      Subgoals provable by reflexivity are dispensed automatically.
      The goal can also be a homogenous equality. New subgoals will use homogenous equalities where possible. -/
  meta def congr_args : tactic unit :=
  do tgt ← target,
     (lhs, rhs) ← match tgt with
     | ```(%%lhs = %%rhs) := pure (lhs, rhs)
     | ```(%%lhs == %%rhs) := pure (lhs, rhs)
     | _ := fail "goal is not an equality"
     end,
     pre ← common_app_prefix lhs rhs,
     l ← mk_hcongr_lemma pre,
     tactic.apply l.proof,
     all_goals $ try refl

  /-- Given a goal that equates two structure values, this tactic breaks it down to subgoals equating each
      pair of fields. -/
  meta def congr_struct : tactic unit :=
  do ```(%%lhs = %%rhs) ← target | fail "goal is not an equality",
     ty ← infer_type lhs,
     eta ← mk_struct_eta ty,
     apply ``(@eq.rec _ _ (λ lhs, lhs = %%rhs) _ _ %%(app eta lhs)),
     ```(%%new_lhs = %%rhs) ← target,
     apply ``(@eq.rec _ _ (λ rhs, %%new_lhs = rhs) _ _ %%(app eta rhs)),
     congr_args
end tactic.interactive

structure X { a : Type } ( b : a × a ) := ( c : nat ) 

def foo ( x y : X (1, 1) ) : x = y :=
begin
  congr_struct
end