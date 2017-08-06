open tactic
meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply
   
structure Bijection ( U V : Type ) :=
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v )

class Finite ( α : Type ) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )

lemma empty_exfalso (x : false) : empty := begin exfalso, trivial end

instance empty_is_Finite : Finite empty := {
  cardinality := 0,
  bijection := begin
                 fsplit, 
                 intros, 
                 induction a,
                 intros,
                 induction a,
                 apply empty_exfalso,
                 cases is_lt,
                 intros, 
                 induction u,
                 intros,
                 induction v,
                 cases is_lt,
              end
}