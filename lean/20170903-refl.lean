notation `♮` := by admit
notation `♯`  := by admit

structure {u v} Category :=
  ( Obj : Type u )
  ( Hom : Obj → Obj → Type v )
  ( identity : Π X : Obj, Hom X X )
  ( compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z )

  ( left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f )
  ( right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f )
  ( associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )
    
attribute [simp] Category.left_identity
attribute [simp] Category.right_identity

structure {u1 v1 u2 v2} Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C.Obj),
    onMorphisms (C.identity X) = D.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C.Obj } (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

structure {u1 v1 u2 v2} Full     { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( preimage : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), C.Hom X Y )
  ( witness  : ∀ { X Y : C.Obj } ( f : D.Hom (F.onObjects X) (F.onObjects Y) ), F.onMorphisms (preimage f) = f )

attribute [simp,ematch] Full.witness

structure {u1 v1 u2 v2} Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) :=
  ( injectivity : ∀ { X Y : C.Obj } ( f g : C.Hom X Y ) ( p : F.onMorphisms f = F.onMorphisms g ), f = g )

definition {u1 v1 u2 v2} Embedding { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) := (Full F) × (Faithful F)

structure Idempotent ( C : Category ) :=
   ( object : C.Obj )
   ( idempotent : C.Hom object object )
   ( witness : C.compose idempotent idempotent = idempotent )

attribute [simp,ematch] Idempotent.witness

definition IdempotentCompletion ( C: Category ) : Category :=
{
  Obj            := Idempotent C,
  Hom            := λ X Y, { f : C.Hom X.object Y.object // C.compose X.idempotent f = f ∧ C.compose f Y.idempotent = f },
  identity       := λ X, ⟨ X.idempotent, ♮ ⟩,
  compose        := λ X Y Z f g, ⟨ C.compose f.val g.val, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

definition functor_to_IdempotentCompletion ( C : Category ) : Functor C (IdempotentCompletion C) := {
  onObjects     := λ X, ⟨ X, C.identity X, ♮ ⟩,
  onMorphisms   := λ _ _ f, ⟨ f, ♮ ⟩,
  identities    := ♮,
  functoriality := ♮
}

open tactic
meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply

meta def second {α} (t : tactic α) : tactic unit :=
tactic.focus [ skip, t >>= (λ a, skip)]

-- attribute [simp] id_locked_eq

lemma embedding_in_IdempotentCompletition ( C: Category ) : Full (functor_to_IdempotentCompletion C) :=
begin
    fsplit, 
    intros, 
    dsimp at * {unfold_reducible := tt, md := semireducible}, 
    induction f, 
    simp at *, 
    tactic.focus [ `[skip], `[intros] ], 
    tactic.focus [ `[skip], `[fapply subtype.eq]], 
    tactic.focus [ `[skip], `[dsimp {unfold_reducible := tt, md := semireducible}]], 
    tactic.focus [ `[skip], `[dsimp at * {unfold_reducible := tt, md := semireducible}]], 
    tactic.focus [ `[skip], `[induction f]], 
    tactic.focus [ `[skip], `[dsimp {unfold_reducible := tt, md := semireducible}]],

    -- tidy {trace_result:=tt},
    exact val,
    refl, -- FIXME this really should work!



    fsplit,
    intros, 
    dsimp at * {unfold_reducible := tt, md := semireducible},
    induction f,
    simp at *,

    second (intros),
    second `[fapply subtype.eq],
    second `[dsimp {unfold_reducible := tt, md := semireducible}],
    second `[dsimp at * {unfold_reducible := tt, md := semireducible}],
    second `[induction f],
    second `[induction property],
    second `[dsimp {unfold_reducible := tt, md := semireducible}],

    exact val,
    refl, -- FIXME this really should work!
end