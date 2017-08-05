namespace tactic

meta def unfold_projections_core (m : transparency) (max_steps : nat) (e : expr) : tactic expr :=
let unfold (changed : bool) (e : expr) : tactic (bool × expr × bool) := do
  new_e ← unfold_projection_core m e,
  return (changed ∨ (new_e ≠ e), new_e, tt)
in do (tt, new_e) ← dsimplify_core ff default_max_steps tt (λ c e, failed) unfold e | fail "no projections to unfold",
      return new_e

meta def unfold_projections : tactic unit :=
target >>= unfold_projections_core semireducible default_max_steps >>= change

meta def unfold_projections_at (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← unfold_projections_core semireducible default_max_steps d,
   change $ expr.pi n bi new_d b,
   intron num_reverted
end tactic

namespace tactic.interactive
open tactic
open lean.parser
open interactive
open interactive.types

private meta def unfold_projections_hyps : list name → tactic unit
| []      := skip
| (h::hs) := get_local h >>= unfold_projections_at >> unfold_projections_hyps hs

meta def unfold_projections : parse location → tactic unit
| [] := tactic.unfold_projections
| hs := unfold_projections_hyps hs
end tactic.interactive

-- Now we try these out:

structure X := ( α : Type )

def x : X := { α := empty }

-- This works fine:
def f : x.α → nat := begin unfold_projections, intros, induction a end
-- This should, but doesn't:
def g : x.α → nat := begin intros, unfold_projections at a, induction a end

