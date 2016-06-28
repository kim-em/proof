(* it is a bit strange that we treat source and target
as a property of a functor, rather than... part of the
typing information? *)

Require Import CpdtTactics.
Set Implicit Arguments.

Structure Category := {
  object: Type;
  hom: object -> object -> Type;
  identity: forall a: object, hom(a)(a);
  composition:
    forall a b c: object,
      hom(a)(b) -> hom(b)(c) -> hom(a)(c);
  leftIdentities:
    forall a b: object,
    forall f: hom(a)(b),
      composition(identity(a))(f) = f;
  rightIdentities:
    forall a b: object,
    forall f: hom(a)(b),
      composition(f)(identity(b)) = f;
  associativity:
    forall a b c d: object,
    forall f: hom(a)(b),
    forall g: hom(b)(c),
    forall h: hom(c)(d),
    composition(composition(f)(g))(h) = composition(f)(composition(g)(h))
}.

Structure Functor(source target: Category) := {
  onObjects: source.(object) -> target.(object);
  onMorphisms: forall x y: source.(object),
    source.(hom)(x)(y) -> target.(hom)(onObjects(x))(onObjects(y));
  identities: forall x: source.(object),
    onMorphisms(x)(x)(source.(identity)(x)) = target.(identity)(onObjects(x));
  functoriality:
    forall x y z: source.(object),
    forall f: source.(hom)(x)(y),
    forall g: source.(hom)(y)(z),
      onMorphisms(x)(z)(source.(composition)(x)(y)(z)(f)(g)) = target.(composition)(onObjects(x))(onObjects(y))(onObjects(z))(onMorphisms(x)(y)(f))(onMorphisms(y)(z)(g))
}.

(* Can we use pattern matching in the arguments, instead of writing fst and snd everywhere? *)

Program Definition CartesianProduct(C: Category)(D: Category): Category := {|
  object := (C.(object) * D.(object)) % type;
  hom := fun p q => ((hom C (fst p) (fst q)) * (hom D (snd p) (snd q))) % type;
  identity := fun p => (identity C (fst p), identity D (snd p));
  composition := fun a b c f g => (C.(composition) (fst a) (fst b) (fst c) (fst f) (fst g), D.(composition) (snd a) (snd b) (snd c) (snd f) (snd g));
  leftIdentities := _;
  rightIdentities := _;
  associativity := _
|}.
Next Obligation.
  pose (leftIdentities C).
  pose (leftIdentities D).
  crush.
Defined.
Next Obligation.
  pose (rightIdentities C).
  pose (rightIdentities D).
  crush.
Defined.
Next Obligation.
  pose (associativity C).
  pose (associativity D).
  crush.
Defined.

(*
Program Definition castObject { C D: Category } ( Q: C = D ) ( a: C.(object) ) : D.(object) := _.
Program Definition castMorphism { C D: Category } ( Q: C = D ) { x y: C.(object) } ( a: C.(hom) x y ) : D.(hom) (castObject Q x) (castObject Q y) := _.
*)

(* of course, this isn't the full definition of lax; we need an associativity constraint still! *)
(* to define the strong case, we need to go back and talk about identities and isomorphisms *)

Structure LaxMonoidalCategory := {
  underlying: Category;
  tensor: Functor (CartesianProduct underlying underlying) underlying;
  associator:
    forall x y z: underlying.(object),
    underlying.(hom)(
      (tensor.(onObjects)((tensor.(onObjects)(x,y)), z))
    )(
      (tensor.(onObjects)(x, (tensor.(onObjects)(y,z))))
    );
  pentagon:
    forall w x y z: underlying.(object),
    composition underlying associator(onObjects tensor (w,x))(y)(z) associator(w)(x)(onObjects tensor (y,z)) =
    composition underlying (
      composition underlying (
        ???,
        ???
      ),
      ???
    );
  (* still todo: pentagon ... *)
}.
