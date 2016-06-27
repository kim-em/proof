Definition zero(x: nat) := 
  match x with 0 => True | _ => False end
.

Check zero.

Definition f(x:nat)(y: zero x) := x + 1.

Check f.

Structure Category := {
  object: Type;
  hom: object -> object -> Type;
  composition:
    forall a b c: object,
      hom(a)(b) -> hom(b)(c) -> hom(a)(c);
  associativity:
    forall a b c d: object,
    forall f: hom(a)(b),
    forall g: hom(b)(c),
    forall h: hom(c)(d),
    composition(a)(c)(d)(composition(a)(b)(c)(f)(g))(h) = composition(a)(b)(d)(f)(composition(b)(c)(d)(g)(h))
}.

Check Category.

Print Category.

Require Import Arith.
SearchRewrite ((_ + _) + _).
Check plus_assoc_reverse.

(* Notice the use of jokers in the definition of 'composition' and 'associativity' below.
   It would be even nicer if we could omit them entirely; implicit arguments? *)

Definition NaturalsAsCategory := {|
  object := True;
  hom := fun(a: True)(b: True) => nat;
  composition := fun _ _ _ f g => f + g;
  associativity := fun _ _ _ _ f g h => plus_assoc_reverse(f)(g)(h);
|}.

Structure Functor := {
  source: Category;
  target: Category;
  onObjects: source.(object) -> target.(object);
  onMorphisms: forall x y: source.(object),
    source.(hom)(x)(y) -> target.(hom)(onObjects(x))(onObjects(y));
  functoriality:
    forall x y z: source.(object),
    forall f: source.(hom)(x)(y),
    forall g: source.(hom)(y)(z),
      onMorphisms(x)(z)(source.(composition)(x)(y)(z)(f)(g)) = target.(composition)(onObjects(x))(onObjects(y))(onObjects(z))(onMorphisms(x)(y)(f))(onMorphisms(y)(z)(g));
}.

SearchRewrite (_ * (_ + _) ).


Definition DoublingAsFunctor := {|
  source := NaturalsAsCategory;
  target := NaturalsAsCategory;
  onObjects := fun(a: True) => a;
  onMorphisms := fun _ _ x => 2 * x;
  functoriality :=  fun _ _ _ f g => Nat.mul_add_distr_l(2)(f)(g);
|}.

SearchRewrite (_ = _, _ = _).
SearchRewrite (_ = _ /\ _ = _).
SearchRewrite ((_, _) = (_, _)).

Check injective_projections.


Lemma pair_equality_0: forall t: Type, forall a b c d: t, a = b /\ c = d -> (a,c) = (b,d).
intros t a b c d [h1 h2].
apply injective_projections.
admit.
admit.
Admitted.

Require Import CpdtTactics.

Lemma pair_equality_1: forall t: Type, forall a b c d: t, a = b /\ c = d -> (a,c) = (b,d).
crush.
Qed.

(* Can use pattern matching in the arguments, instead of writing fst and snd everywhere? *)

Definition CartesianProduct(C: Category)(D: Category): Category := {|
  object := (C.(object) * D.(object)) % type;
  hom := fun p q => ((hom C (fst p) (fst q)) * (hom D (snd p) (snd q))) % type;
  composition := fun a b c f g => (C.(composition) (fst a) (fst b) (fst c) (fst f) (fst g), D.(composition) (snd a) (snd b) (snd c) (snd f) (snd g));
  associativity := fun a b c d f g h => 
    (
      C.(associativity) (fst a) (fst b) (fst c) (fst d) (fst f) (fst g) (fst h),
      D.(associativity) (snd a) (snd b) (snd c) (snd d) (snd f) (snd g) (snd h)
    );
|}

(* What is the Coq equivalent of ??? *)

(* Is there a more succinct way of specifying the source and target here? *)
(* of course, this isn't the full definition of lax; we need an associativity constraint still! *)
(* to define the strong case, we need to go back and talk about identities and isomorphisms *)

Definition LaxMonoidalCategory := {
  underlying: Category;
  tensor: Functor;
  tensorSource: tensor.(source) = CartesianProduct(underlying)(underlying);
  tensorTarget: tensor.(target) = underlying;
  associator:
    forall x y z: underlying.(object),
    underlying.(hom)(tensor.(onObjects)((tensor.(onObjects)((x,y))), z))(tensor.(onObjects)((x, tensor.(onObjects)((y,z)))))
}