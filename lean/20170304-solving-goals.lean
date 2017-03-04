open tactic
open smt_tactic

notation `♮` := by abstract { using_smt $ intros >> try simp }

structure Monoid ( α : Type ) :=
  (one : α)
  (compose  : α → α → α)
  (left_identity  : ∀ ( f : α ), compose one f = f)
  (right_identity : ∀ ( f : α ), compose f one = f)
  (associativity  : ∀ ( f g h : α ),
    compose (compose f g) h = compose f (compose g h))

definition NaturalsAsMonoid : Monoid ℕ := {
  compose  := λ a b, a + b,
  one      := 0,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}