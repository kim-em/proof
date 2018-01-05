structure {u v} Category :=
  ( Obj : Type u )
  ( Hom : Obj → Obj → Type v )
  ( identity : Π X : Obj, Hom X X )
  ( compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z )
  ( left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f )
    
attribute [simp] Category.left_identity

structure {u1 v1 u2 v2} Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))

structure {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( preimage : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), C.Hom X Y )
  ( witness  : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), F.onMorphisms (preimage f) = f )

structure Idempotent ( C : Category ) :=
   ( object : C.Obj )
   ( idempotent : C.Hom object object )

definition IdempotentCompletion ( C: Category ) : Category :=
{
  Obj            := Idempotent C,
  Hom            := λ X Y, { f : C.Hom X.object Y.object // C.compose X.idempotent f = f ∧ C.compose f Y.idempotent = f },
  identity       := λ X, ⟨ X.idempotent, sorry ⟩,
  compose        := λ X Y Z f g, ⟨ C.compose f.val g.val, sorry ⟩,
  left_identity  := sorry
}

definition functor_to_IdempotentCompletion ( C : Category ) : Functor C (IdempotentCompletion C) := {
  onObjects     := λ X, ⟨ X, C.identity X ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, sorry ⟩
}

open tactic

-- fsplit is just split, but we use fapply on the constructors, rather than apply.
-- This is essential so we actually get given all the goals, rather than some of them turning into metavariables.
meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply >> skip

lemma embedding_in_IdempotentCompletition ( C: Category ) : Full (functor_to_IdempotentCompletion C) :=
begin
fsplit, 
intros, 
dsimp at * {md := semireducible}, 
induction f,
simp at *, 
 -- now, perversely, we run some tactics on the second goal, before closing the first goal
 any_goals {intros},
 any_goals {fapply subtype.eq},
 any_goals {dsimp},
 any_goals {dsimp at * {md := semireducible}},
 any_goals {induction f},
 any_goals {dsimp},
-- finally, we actually get to business.
exact f_val,
refl,
end
