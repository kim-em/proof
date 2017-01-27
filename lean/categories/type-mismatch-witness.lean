meta def blast : tactic unit := using_smt $ return ()

structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))


namespace workaround1
/-
Declare notation for applying "type casts" using objectWitness.

Cons: it is verbose.
-/

def transportHom
 {C D : Category} {F G : Functor C D}
 (objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
 {X Y : C^.Obj}
 (h : D^.Hom (F^.onObjects X) (F^.onObjects Y)) : D^.Hom (G^.onObjects X) (G^.onObjects Y) :=
eq.rec_on (objectWitness X) (eq.rec_on (objectWitness Y) h)

infix `►`:60 := transportHom

lemma Functors_pointwise_equal
  { C D : Category }
  { F G : Functor C D }
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, objectWitness ► F^.onMorphisms f = G^.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  rewrite h_objects at F_onMorphisms,
  assert h_morphisms : F_onMorphisms = G_onMorphisms, exact funext morphismWitness,
  exact sorry
end

end workaround1

namespace workaround2
/-
Use heterogeneous equality.
We can convert a heterogeneous equality back into a homogeneous one, if we can prove the types are equal.

Cons: it is easy to make mistakes. For example, given (a : nat) (s : string) (h : a == s), the hypothesis
h is probably a mistake, but Lean will not complain.
-/

lemma Functors_pointwise_equal
  { C D : Category }
  { F G : Functor C D }
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, F^.onMorphisms f == G^.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  rewrite h_objects at F_onMorphisms,
  assert h_morphisms : F_onMorphisms = G_onMorphisms, exact funext morphismWitness,
  exact sorry
end

end workaround2

namespace workaround3
/-
Write a tactic for automatically generating the type casts, and notation for invoking it.
Cons: the tactic may create "ugly" proofs, and these proofs will be nested in the 
statement of your theorem.
-/

open smt_tactic
/- Very simple tactic that uses hypotheses from the local context for performing 3
   rounds of heuristic instantiation, and congruence closure. -/
meta def simple_tac : tactic unit :=
using_smt $ intros >> add_lemmas_from_facts >> repeat_at_most 3 ematch

/- Version of cast operator that "hides" the "ugly" proof -/
def {u} auto_cast {α β : Type u} {h : α = β} (a : α) :=
cast h a

notation `⟦` p `⟧` := @auto_cast _ _ (by simple_tac) p

lemma Functors_pointwise_equal
  { C D : Category }
  { F G : Functor C D }
  ( objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, ⟦ F^.onMorphisms f ⟧ = G^.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  rewrite h_objects at F_onMorphisms,
  assert h_morphisms : F_onMorphisms = G_onMorphisms, exact funext morphismWitness,
  exact sorry
end


print Functors_pointwise_equal

end workaround3