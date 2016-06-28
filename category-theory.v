Require Import CpdtTactics.

Set Implicit Arguments.

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
    composition(composition(f)(g))(h) = composition(f)(composition(g)(h))
}.

Program Definition NaturalsAsCategory := {|
  object := True;
  hom := fun(a: True)(b: True) => nat;
  composition := fun _ _ _ f g => f + g;
  associativity := _
|}.
Next Obligation.
  crush.
Defined.

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
      onMorphisms(x)(z)(source.(composition)(x)(y)(z)(f)(g)) = target.(composition)(onObjects(x))(onObjects(y))(onObjects(z))(onMorphisms(x)(y)(f))(onMorphisms(y)(z)(g))
}.



Program Definition DoublingAsFunctor := {|
  source := NaturalsAsCategory;
  target := NaturalsAsCategory;
  onObjects := fun(a: True) => a;
  onMorphisms := fun _ _ x => 2 * x;
  functoriality := _
|}.
Next Obligation.
  crush.
Defined.

(* Can use pattern matching in the arguments, instead of writing fst and snd everywhere? *)

Program Definition CartesianProduct(C: Category)(D: Category): Category := {|
  object := (C.(object) * D.(object)) % type;
  hom := fun p q => ((hom C (fst p) (fst q)) * (hom D (snd p) (snd q))) % type;
  composition := fun a b c f g => (C.(composition) (fst a) (fst b) (fst c) (fst f) (fst g), D.(composition) (snd a) (snd b) (snd c) (snd f) (snd g));
  associativity := _
|}.
Next Obligation.
  pose (assocC := associativity C).
  pose (assocD := associativity D).
  crush.
Defined.

Check CartesianProduct.

(* Is there a more succinct way of specifying the source and target here? *)
(* of course, this isn't the full definition of lax; we need an associativity constraint still! *)
(* to define the strong case, we need to go back and talk about identities and isomorphisms *)

Structure LaxMonoidalCategory := {
  underlying: Category;
  tensor: Functor;
  tensorSource: tensor.(source) = CartesianProduct(underlying)(underlying); 
  tensorTarget: tensor.(target) = underlying; 
  associator:
    forall x y z: underlying.(object),
    underlying.(hom)(tensor.(onObjects)((tensor.(onObjects)((x,y))), z))(tensor.(onObjects)((x, tensor.(onObjects)((y,z)))));
  (* pentagon ... *)
}.
