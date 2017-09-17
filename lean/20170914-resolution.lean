open tactic
open nat

universe variables u v w

-- TODO is this in the standard library?
meta definition interaction_monad.result.map { α σ σ' : Type } (r : interaction_monad.result σ α) (f : σ → σ') : interaction_monad.result σ' α :=
match r with 
| result.success   a       s := result.success   a       (f s)
| result.exception msg pos s := result.exception msg pos (f s)
end

meta instance interaction_monad.alternative (σ : Type): alternative (interaction_monad (tactic_state × σ)) := {
  @interaction_monad.monad (tactic_state × σ) with
  orelse := λ { α : Type } (t₁ t₂ : interaction_monad (tactic_state × σ) α) s, 
              match (t₁ s) with
              | result.success   a       s' := result.success a s'
              | result.exception msg pos s' := (t₂ (s.1, s'.2))    -- we discard the tactic_state from the failed branch, but keep the other state
              end,
  failure := λ { α : Type }, interaction_monad.failed,
}

meta class underlying_tactic_state ( σ : Type ) :=
  ( to_tactic_state : σ → tactic_state )

meta instance trivial_underlying_tactic_state : underlying_tactic_state tactic_state :=
{ to_tactic_state := id }

meta instance product_underlying_tactic_state ( σ τ : Type ) [underlying_tactic_state σ]: underlying_tactic_state (σ × τ) :=
{ to_tactic_state := λ p, underlying_tactic_state.to_tactic_state p.1 }

meta class tactic_lift ( τ : Type ) :=
  ( lift : Π { σ α : Type } [underlying_tactic_state σ], interaction_monad σ α → interaction_monad (σ × τ) α )

meta def pack_states {σ τ ρ α : Type}: interaction_monad ((σ × τ) × ρ) α → interaction_monad (σ × (τ × ρ)) α :=
λ t s, (t ((s.1, s.2.1), s.2.2)).map(λ s', (s'.1.1, (s'.1.2, s'.2)))

meta def unpack_states {σ τ ρ α : Type}: interaction_monad (σ × (τ × ρ)) α → interaction_monad ((σ × τ) × ρ) α :=
λ t s, (t (s.1.1, (s.1.2, s.2))).map(λ s', ((s'.1, s'.2.1), s'.2.2))

meta instance tactic_lift_product ( τ τ' : Type ) [tactic_lift τ] [tactic_lift τ'] : tactic_lift (τ × τ') := {
  lift := λ { σ α } [uts : underlying_tactic_state σ] t, pack_states (@tactic_lift.lift τ' _ _ _ (@product_underlying_tactic_state _ _ uts) (@tactic_lift.lift τ _ _ _ uts t))
}

meta instance tactic_lift_coe (τ : Type) [tactic_lift τ] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad (σ × τ) α) :=
⟨ tactic_lift.lift τ ⟩

set_option trace.class_instances true

set_option class.instance_max_depth 50

#print fail

meta def monadic_chain { σ : Type } [ lift : tactic_lift σ ] : interaction_monad (tactic_state × σ) unit := 
tactic_lift.lift _ (fail  "")